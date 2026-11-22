#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r11_warmstart_gate.py — R11B warm-start 探针验收门（G1–G6 ＋ NC1/NC2）.

任务书口径（r11b-warmstart-probe，D43 裁决 2）：SDPA-GMP warm-start 通道
端到端死活探针的交付质量与证据链一致性门——不验实验结局（alive/dead/
ignored 两结局均有效交付）。ledger＝numerics/bounds/results/
r11_warmstart_probe.json（warmstart_probe.py 产出）。

检查面（全部确定性；seed 20261013 按惯例记档，本门无随机路径）：
  G1 ledger 完整：runs ≥ 2 且每 run 含 solve_s/iterations/objVal/phase/
     phase_value 全字段；verdict ∈ {channel_alive, channel_dead,
     channel_ignored}；消费规则文案在档
  G2 冷重解确定性口径：cold.iterations == 76，或 determinism.
     determinism_deviation == true 且解释非空（附：表逐位同档字段在档）
  G3 消费推断与数据一致：consumption.consumed ⇔（warm_self 迭代 ≠ cold
     迭代）。迭代数优先从 .result 落盘文件独立复读（在盘时；复读值与
     ledger 失配即 fail），文件不在盘时退回 ledger 值并注明
  G4 verdict 分支证据完备：
     alive  ⇒ cert.verify_cert_exit == 0 ＋ quality.objVal_match == true
              ＋ certified 与存档 claimed_bound 逐位（字符串相等）
     ignored ⇒ warm_self.iterations == cold.iterations 在档
               （iterations_equal_cold 证据）＋ stderr 摘要在档
     dead   ⇒ warm_self.stderr_summary 在档（求解失败/错误摘要证据）
  G5 预算：Σ runs.solve_s 以 Fraction 精确求和 ≤ 2160s（口径 A 硬顶）
  G6 冻结件零改动：ledger.frozen_sha256（探针首录）与现盘 sha256 逐件
     一致 ＋ frozen_sha256_after（探针尾录）一致 ＋ git HEAD 对冻结路径
     零 diff 零未跟踪（typed_ladder_work/、typed_ladder.json、
     typed_ladder_sol_m090_M6.json、lp.json、n9-stage-a4-typedcap-m090_M6
     .json 五面）
  NC1 篡改 consumed 标志：ledger 副本翻转 consumption.consumed ⇒ G3 必须
      拦（exit 1）
  NC2 /tmp 伪造同迭代 .result：伪造 warm .result（Iteration == cold 76）
      ＋声称 consumed=true 的伪 ledger ⇒ G3 文件复读路径必须拦（exit 1）

用法：
  python3 numerics/bounds/r11_warmstart_gate.py            # 全门（exit 0 = 过）
  python3 numerics/bounds/r11_warmstart_gate.py --ledger PATH  # 对副本跑门
  python3 numerics/bounds/r11_warmstart_gate.py --no-nc     # 跳过 NC
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
LEDGER_DEFAULT = HERE / "results" / "r11_warmstart_probe.json"

SEED_GATE = 20261013                     # 惯例记档；本门无随机路径（确定性）
BUDGET_CAP_S = Fraction(2160)            # 口径 A 硬顶
ARCH_ITER = 76                           # 存档冷解迭代数（typed_ladder_sol_m090_M6）
VERDICTS = {"channel_alive", "channel_dead", "channel_ignored"}
RUN_FIELDS = ["solve_s", "iterations", "objVal", "phase", "phase_value"]

FROZEN = [
    "numerics/bounds/results/typed_ladder_work",
    "numerics/bounds/results/typed_ladder.json",
    "numerics/bounds/results/typed_ladder_sol_m090_M6.json",
    "numerics/bounds/results/lp.json",
    "certificates/n9-stage-a4-typedcap-m090_M6.json",
]

CHECKS: list[str] = []


def ok(msg: str) -> None:
    print(f"[gate][ OK ] {msg}", flush=True)


def fail(msg: str) -> None:
    print(f"[gate][FAIL] {msg}", flush=True)
    sys.exit(1)


def sha256_of(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def read_iterations_from_result(path: Path) -> int:
    """独立复读 .result 的 Iteration 行（消费证据文件面）。"""
    text = path.read_text()
    mm = re.search(r"^\s*Iteration = (\d+)\s*$", text, re.M)
    if not mm:
        fail(f"复读 {path}：Iteration 行缺失")
    return int(mm.group(1))


def derive_iterations(led: dict, phase: str, default):
    """G3 迭代数：盘上 .result 复读优先（并与 ledger 交叉核对），否则 ledger。"""
    row = next((r for r in led["runs"] if r["phase"] == phase), None)
    if row is None:
        fail(f"G3: runs 缺 {phase} 行")
    rp = row.get("result_path")
    if rp and Path(rp).exists():
        it_file = read_iterations_from_result(Path(rp))
        if it_file != row["iterations"]:
            fail(f"G3: {phase} ledger 迭代 {row['iterations']} ≠ 文件复读 "
                 f"{it_file}（{rp}）——账实不符")
        return it_file, "file"
    return row["iterations"], "ledger"


def check_g3(led: dict) -> tuple[bool, str]:
    """消费推断一致性（NC1/NC2 复用）。返回 (通过, 说明)。"""
    cold_it, src_c = derive_iterations(led, "cold", None)
    warm_it, src_w = derive_iterations(led, "warm_self", None)
    claimed = led.get("consumption", {}).get("consumed")
    if claimed is None:
        return False, "consumption.consumed 缺失"
    actual = (warm_it != cold_it) and (warm_it is not None) and (cold_it is not None)
    if claimed != actual:
        return False, (f"consumed={claimed} 与数据矛盾：cold={cold_it}（{src_c}）"
                       f" warm={warm_it}（{src_w}）⇒ 实际 consumed 应为 {actual}")
    return True, (f"cold={cold_it}（{src_c}） warm={warm_it}（{src_w}） ⇒ "
                  f"consumed={claimed} 一致")


def run_gate(ledger_path: Path, with_nc: bool = True) -> None:
    led = json.loads(ledger_path.read_text())

    # ---------------- G1 ledger 完整
    runs = led.get("runs", [])
    if len(runs) < 2:
        fail(f"G1: runs {len(runs)} < 2")
    for r in runs:
        for f in RUN_FIELDS:
            if r.get(f) in (None, ""):
                fail(f"G1: run[{r.get('phase')}] 缺字段 {f}")
    if led.get("verdict") not in VERDICTS:
        fail(f"G1: verdict={led.get('verdict')} 不在三值集")
    if "迭代数" not in str(led.get("consumption", {}).get("rule", "")):
        fail("G1: 消费规则文案（迭代数≠）不在档")
    ok(f"G1 ledger 完整：runs={len(runs)}（{[r['phase'] for r in runs]}），"
       f"verdict={led['verdict']}")

    # ---------------- G2 冷重解确定性口径
    det = led.get("determinism", {})
    cold_it_led = next(r["iterations"] for r in runs if r["phase"] == "cold")
    if cold_it_led == ARCH_ITER:
        if det.get("determinism_deviation") and not det.get("explanation"):
            fail("G2: determinism_deviation=true 但解释为空")
        ok(f"G2 冷重解确定性：iterations={cold_it_led} == 存档 {ARCH_ITER}；"
           f"表逐位同档={det.get('table_identical_to_archive')}")
    elif det.get("determinism_deviation") is True and det.get("explanation"):
        ok(f"G2 冷重解偏离在档：iterations={cold_it_led}，解释："
           f"{det['explanation'][:120]}")
    else:
        fail(f"G2: cold.iterations={cold_it_led} ≠ {ARCH_ITER} 且无偏离解释"
             "（determinism_deviation=true 附解释二缺一）")

    # ---------------- G3 消费推断与数据一致
    g3_ok, g3_msg = check_g3(led)
    if not g3_ok:
        fail(f"G3: {g3_msg}")
    ok(f"G3 消费推断与数据一致：{g3_msg}")

    # ---------------- G4 verdict 分支证据完备
    v = led["verdict"]
    cert = led.get("cert", {})
    qual = led.get("quality", {})
    if v == "channel_alive":
        if cert.get("verify_cert_exit") != 0:
            fail(f"G4: alive 但 verify-cert exit={cert.get('verify_cert_exit')}")
        if qual.get("objVal_match") is not True:
            fail("G4: alive 但 objVal 未对上存档")
        if qual.get("certified") != qual.get("archived_claimed_bound"):
            fail("G4: alive 但 certified 与存档 claimed_bound 非逐位相等")
        ok(f"G4 alive 证据完备：verify-cert exit 0＋objVal 对上＋certified 逐位"
           f"（{qual.get('certified')}）")
    elif v == "channel_ignored":
        cons = led.get("consumption", {})
        if cons.get("iterations_equal_cold") is not True:
            fail("G4: ignored 但 iterations_equal_cold 证据不在档")
        ws_row = next(r for r in runs if r["phase"] == "warm_self")
        if not ws_row.get("stderr_summary"):
            fail("G4: ignored 但 warm stderr 摘要不在档")
        ok("G4 ignored 证据完备：迭代相等（"
           f"cold={cons.get('cold_iterations')} warm={cons.get('warm_iterations')}"
           "）＋stderr 摘要在档")
    else:  # channel_dead
        ws_row = next(r for r in runs if r["phase"] == "warm_self")
        if not ws_row.get("stderr_summary"):
            fail("G4: dead 但 warm stderr 摘要不在档")
        ok(f"G4 dead 证据完备：stderr 摘要在档（{ws_row['stderr_summary'][:80]}…）"
           f"；verdict_reason={str(led.get('verdict_reason'))[:100]}")

    # ---------------- G5 预算（Fraction 精确）
    total = Fraction(0)
    for r in runs:
        try:
            total += Fraction(str(r["solve_s"]))
        except (ValueError, ZeroDivisionError) as exc:
            fail(f"G5: solve_s={r['solve_s']!r} 非法（{r['phase']}）：{exc}")
    if total > BUDGET_CAP_S:
        fail(f"G5: Σsolve_s = {total} > {BUDGET_CAP_S}s 硬顶")
    ok(f"G5 预算：Σsolve_s = {total} ≤ {BUDGET_CAP_S}s（Fraction 精确；"
       f"{len(runs)} runs 计入）")

    # ---------------- G6 冻结件零改动
    for name, rec in led.get("frozen_sha256", {}).items():
        p = Path(rec["path"])
        if not p.exists():
            fail(f"G6: 冻结件不在盘：{p}")
        now = sha256_of(p)
        if now != rec["sha256"]:
            fail(f"G6: {name} sha256 前后失配（首录 {rec['sha256'][:16]}… vs "
                 f"现盘 {now[:16]}…）")
        after = led.get("frozen_sha256_after", {}).get(name)
        if after != rec["sha256"]:
            fail(f"G6: {name} 探针尾录 sha256 与首录不一致")
    for fpath in FROZEN:
        d = subprocess.run(["git", "-C", str(REPO), "diff", "HEAD", "--", fpath],
                           capture_output=True, text=True)
        s = subprocess.run(["git", "-C", str(REPO), "status", "--porcelain",
                            "--", fpath], capture_output=True, text=True)
        if d.returncode != 0 or s.returncode != 0:
            fail(f"G6: git 守卫命令失败（{fpath}）：{d.stderr}{s.stderr}")
        if d.stdout.strip() or s.stdout.strip():
            fail(f"G6: 冻结路径有改动/未跟踪：{fpath}\n{d.stdout}{s.stdout}")
    ok(f"G6 冻结件零改动：{len(led.get('frozen_sha256', {}))} 件 sha256 前后一致"
       f"＋git HEAD 零 diff（{len(FROZEN)} 路径守卫）")

    # ---------------- NC1 篡改 consumed 标志必被 G3 拦
    if with_nc:
        with tempfile.NamedTemporaryFile("w", suffix=".json",
                                         delete=False) as fh:
            tampered = json.loads(json.dumps(led))
            tampered["consumption"]["consumed"] = \
                not tampered["consumption"]["consumed"]
            fh.write(json.dumps(tampered))
            ncp1 = Path(fh.name)
        rc = subprocess.run([sys.executable, str(Path(__file__).resolve()),
                             "--no-nc", "--ledger", str(ncp1)],
                            capture_output=True, text=True)
        if rc.returncode == 0:
            fail(f"NC1: 篡改 consumed 后门仍 exit 0——G3 未拦：{rc.stdout[-300:]}")
        if "G3" not in rc.stdout:
            fail(f"NC1: 篡改被拦但非 G3 拦截：{rc.stdout[-300:]}")
        ok("NC1 篡改 consumed 标志被 G3 拦截（exit 1，G3 面报错）")

        # ---------------- NC2 /tmp 伪造同迭代 result 必被检出
        with tempfile.TemporaryDirectory(prefix="r11_ws_gate_nc2_") as td:
            td = Path(td)
            forged = td / "forged_warm.result"
            forged.write_text(
                'SDPA-GMP start at Fri Jan 1 00:00:00 2026\n'
                '"forged for NC2 — iteration forged equal to cold"\n'
                f"phase.value = pdOPT\n   Iteration = {ARCH_ITER}\n"
                "mu = 1.0e-30\nrelative gap = 1.0e-79\n"
                "objValPrimal = 2.5753123280579235e+01\n"
                "objValDual   = 2.5753123280579235e+01\n")
            forged_led = json.loads(json.dumps(led))
            ws_row = next(r for r in forged_led["runs"]
                          if r["phase"] == "warm_self")
            ws_row["result_path"] = str(forged)      # 声称暖启产物在此
            ws_row["iterations"] = 12                 # 账面谎报 ≠ cold
            forged_led["consumption"]["consumed"] = True
            forged_led["warm_self"]["iterations"] = 12
            fpath = td / "forged_ledger.json"
            fpath.write_text(json.dumps(forged_led))
            rc2 = subprocess.run([sys.executable, str(Path(__file__).resolve()),
                                  "--no-nc", "--ledger", str(fpath)],
                                 capture_output=True, text=True)
            if rc2.returncode == 0:
                fail(f"NC2: 伪造同迭代 result 未被检出（exit 0）：{rc2.stdout[-300:]}")
            if "G3" not in rc2.stdout and "账实不符" not in rc2.stdout:
                fail(f"NC2: 拦截面非 G3 文件复读：{rc2.stdout[-300:]}")
            ok("NC2 /tmp 伪造同迭代（76）result 被文件复读检出（G3 账实不符/"
               "consumed 矛盾，exit 1）")

    print(f"[gate] PASS —— seed {SEED_GATE}（无随机路径）；ledger="
          f"{ledger_path}", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser(description="R11B warm-start 探针验收门")
    ap.add_argument("--ledger", default=str(LEDGER_DEFAULT))
    ap.add_argument("--no-nc", action="store_true")
    args = ap.parse_args()
    run_gate(Path(args.ledger), with_nc=not args.no_nc)


if __name__ == "__main__":
    main()
