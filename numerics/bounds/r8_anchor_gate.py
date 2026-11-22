#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r8_anchor_gate.py — R8-2 锚定精确取等 (9,6) 判死活探针过门脚本
（裸 python3、seed 20261008、CWD 无关——一切路径由 __file__ 解析、不触发求解：
不调 sdpa、不 import numpy/cvxpy）。先例 moment_gate（1fab129）。

检查序列（exit 0 = 过门）：
  ① 账本完整性：results/anchor_probe_m9.json（schema thomson-n9/bounds/
     anchor-probe/1）、seed、code_version、provenance（commands/sdpa_bin/
     minorant/acceptance）、Arms A+B 在档（C 可选）、R7-1 SCS 基线在档对照；
  ② 幂等：对每臂从存档 sol 重算 e_val/R1/锚定残差/恒等式回读（exact Fraction，
     moment_lift.recompute_anchor_arm 内置逐位断言）＋账本 float 字段与重算值
     逐位（==）一致；
  ③ 判据-数据严格对齐：alive ⟺ Arm B accepted 且 dist=E_ttp−e_val ≤1e-6
     （全精度为主、9 位并列）且卫生全过——独立复算判定并与账本 verdict 比对；
     dead-at-(9,6) 时 M-scaling 比＋M* 外推在档；
  ④ 卫生断言：accepted 臂 e_val ≤ E_ttp+1e-9、R1 ≤1e-12、锚定残差 ≤1e-9、
     (∗) 回读 ≤1e-12（hygiene.all_ok）；
  ⑤ 负对照三件（全部必须被检出，均不求解）：
     (a) 篡改存档 sol 的 e_val（+1e-6）⇒ ② 的幂等重算断言触发（exit 1 语义）；
     (b) 伪造 alive（e=E_ttp+1e-3）⇒ 合法性断言 assert_arm_legality exit 1；
     (c) 删锚定行重放 ⇒ 用无锚定存档解（hermite (7,6) cap，G=0 注入）走同一
         锚定残差计算 ⇒ |λ′(TTP)| > 1e-9 被检出（检出面＝锚定约束真实生效）。
"""
from __future__ import annotations

import json
import random
import subprocess
import sys
import tempfile
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "typed"))
sys.path.insert(0, str(HERE.parents[2] / "thomson-workflow" / "certificates"))

SEED = 20261008
E_TTP = Fraction("25.75998653126983")             # 全精度口径（tube.json，主判据）
E_STAR = Fraction("25.759986531")                 # 9 位口径（energies.json，并列）
R7_1_E = 25.75729578909048                        # R7-1 SCS optimal_inaccurate 旧值
ARCHIVE = HERE / "results" / "anchor_probe_m9.json"

_failures: list[str] = []
_checks = {"passed": 0, "failed": 0}


def check(name: str, ok: bool, detail: str = "") -> bool:
    tag = "PASS" if ok else "FAIL"
    print(f"[gate:{tag}] {name}" + (f" — {detail}" if detail else ""), flush=True)
    if ok:
        _checks["passed"] += 1
    else:
        _checks["failed"] += 1
        _failures.append(f"{name}: {detail}")
    return ok


# ============================================================ ① 账本完整性
def ledger_checks(arch: dict) -> dict:
    check("① 账本在档（schema/kind/seed）",
          arch.get("kind") == "n9-bounds-anchor-probe"
          and arch.get("schema") == "thomson-n9/bounds/anchor-probe/1"
          and arch.get("seed") == SEED,
          f"kind={arch.get('kind')} schema={arch.get('schema')} seed={arch.get('seed')}")
    check("① provenance（code_version/commands/sdpa_bin/minorant/acceptance）",
          bool(arch.get("code_version"))
          and bool(arch.get("provenance", {}).get("commands"))
          and bool(arch.get("provenance", {}).get("sdpa_bin"))
          and "minorant" in arch.get("provenance", {})
          and "acceptance" in arch.get("provenance", {}),
          str(list(arch.get("provenance", {}).keys())))
    arms = arch.get("arms", {})
    check("① Arms A+B 在档（C 可选）", "A" in arms and "B" in arms,
          f"arms={sorted(arms.keys())}")
    v = arch.get("verdict", {})
    r7 = v.get("r7_1_scs_baseline", {})
    check("① R7-1 SCS 基线在档对照（旧值 optimal_inaccurate）",
          abs(float(r7.get("e_val", 0)) - R7_1_E) < 1e-12
          and r7.get("status") == "optimal_inaccurate"
          and bool(v.get("arm_A_replaces_r7_1_baseline")),
          f"r7_1.e_val={r7.get('e_val')}")
    ref = arch.get("reference", {})
    check("① 参考口径（E_ttp 全精度＋9 位并列＋E_anchor）",
          Fraction(ref.get("E_ttp_full", "0")) == E_TTP
          and Fraction(ref.get("E_star_9dp", "0")) == E_STAR
          and bool(ref.get("E_anchor")),
          f"E_ttp−E_anchor={ref.get('E_ttp_minus_E_anchor')}")
    for arm_id in sorted(arms):
        a = arms[arm_id]
        need = ["e_val", "dist_full", "dist_9dp", "R1", "hygiene", "accepted",
                "anchor_lambda_maxrow", "anchor_kernel_max", "identity_readback",
                "readback_exact", "anchor_rows", "cmdline", "solver"]
        missing = [k for k in need if k not in a]
        check(f"① Arm {arm_id} 字段完整（判据/残差/行元数据/provenance）",
              not missing, f"缺 {missing}" if missing else
              f"e_val={a['e_val']:.12f} dist={a['dist_full']:.3e} "
              f"accepted={a['accepted']}")
    return arms


# ============================================================ ② 幂等重算
def idempotence_checks(arms: dict) -> dict:
    import moment_lift as ML
    recs = {}
    for arm_id in sorted(arms):
        sol_path = REPO / arms[arm_id]["sol"]
        try:
            rec = ML.recompute_anchor_arm(sol_path)
            ok, detail = True, ""
        except (SystemExit, AssertionError) as exc:
            rec, ok, detail = None, False, str(exc)[:200]
        check(f"② Arm {arm_id} 幂等重算（存档 sol → exact Fraction 重算逐位一致）",
              ok, detail)
        if not ok:
            continue
        recs[arm_id] = rec
        a = arms[arm_id]
        rb = rec["rb"]
        pairs = [("e_val", float(rec["data"]["e"])),
                 ("dist_full", float(rb["dist_full"])),
                 ("dist_9dp", float(rb["dist_9dp"])),
                 ("anchor_lambda_maxrow", float(rb["lam_resid_maxrow"])),
                 ("anchor_kernel_max", float(rb["kernel_absmax"])),
                 ("identity_readback", float(rb["identity_resid"])),
                 ("nrm_resid", float(rb["nrm"]))]
        pairs += [(f"R1[{o}]", float(v)) for o, v in rb["R1"].items()]
        bad = []
        for (k, v2) in pairs:
            led = (a["R1"][k[3:-1]] if k.startswith("R1[") else a.get(k))
            if led != v2:
                bad.append((k, led, v2))
        check(f"② Arm {arm_id} 账本 float 字段与重算逐位一致（==）", not bad,
              f"不一致 {bad}" if bad else f"{len(pairs)} 字段逐位一致")
        # 锚定残差逐行（16 合并行＝84 逻辑约束的重数合并）：账本 readback_exact
        # 与存档 sol 逐位一致（recompute 已断言 sol 与 exact 重算逐位一致）
        sol_js = json.loads(sol_path.read_text())
        rows_ok = a["readback_exact"] == sol_js["readback"]
        n_rows = len(sol_js["readback"]["lam_rows"])
        check(f"② Arm {arm_id} 锚定 λ 残差 {n_rows} 合并行（×重数＝84 逻辑）账本-sol 逐位一致",
              rows_ok, f"{n_rows} 行 readback_exact 全等")
    return recs


# ============================================================ ③ 判据-数据对齐
def verdict_checks(arch: dict, arms: dict) -> None:
    v = arch.get("verdict", {})
    check("③ verdict 字段合法", v.get("verdict") in ("alive", "dead-at-(9,6)"),
          str(v.get("verdict")))
    check("③ 判据规则文本在档（D13 裁决 2 沿用）", bool(v.get("rule")))
    B = arms["B"]
    alive_expected = bool(B["accepted"]) and B["dist_full"] <= 1e-6 \
        and B["dist_9dp"] <= 1e-6 and bool(B["hygiene"]["all_ok"])
    verdict_expected = "alive" if alive_expected else "dead-at-(9,6)"
    check("③ alive/dead 与 dist 数值严格对应（独立复算判定）",
          v.get("verdict") == verdict_expected,
          f"账本={v.get('verdict')} 独立复算={verdict_expected} "
          f"(B.accepted={B['accepted']}, dist_full={B['dist_full']:.3e}, "
          f"dist_9dp={B['dist_9dp']:.3e}, hygiene.all_ok={B['hygiene']['all_ok']})")
    ms = v.get("m_scaling", {})
    check("③ M-scaling 比（B vs A dist）在档",
          ms.get("dist_A") == arms["A"]["dist_full"]
          and ms.get("dist_B") == arms["B"]["dist_full"]
          and (ms.get("ratio") is None
               or abs(ms["ratio"] - ms["dist_A"] / ms["dist_B"]) < 1e-9),
          f"ratio={ms.get('ratio')}")
    if v.get("verdict") == "dead-at-(9,6)":
        check("③ dead 分支：M* 外推在档（斜率口径）", bool(v.get("M_star")),
              str(v.get("M_star", {}))[:160])


# ============================================================ ④ 卫生断言
def hygiene_checks(arms: dict) -> None:
    for arm_id in sorted(arms):
        a = arms[arm_id]
        h = a["hygiene"]
        if a["accepted"]:
            check(f"④ Arm {arm_id}（accepted）卫生全过（e≤E_ttp+1e-9/R1≤1e-12/"
                  "锚定≤1e-9/(∗)≤1e-12）", bool(h.get("all_ok")),
                  f"e_val−E_ttp={a['e_val'] - float(E_TTP):+.3e} "
                  f"R1max={max(a['R1'].values()):.2e} "
                  f"λmax={a['anchor_lambda_maxrow']:.2e} "
                  f"ker={a['anchor_kernel_max']:.2e} "
                  f"(∗)={a['identity_readback']:.2e}")
        else:
            check(f"④ Arm {arm_id}（未接受）卫生字段如实在档",
                  isinstance(h, dict) and ("all_ok" in h), str(h)[:120])


# ============================================================ ⑤ 负对照三件
def negative_controls(arms: dict) -> None:
    import moment_lift as ML
    # (a) 篡改存档 sol 的 e_val ⇒ 幂等重算断言必须触发
    sol_path = REPO / arms["A"]["sol"]
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td) / sol_path.name
        tampered = json.loads(sol_path.read_text())
        tampered["exact"]["e"] = str(Fraction(tampered["exact"]["e"])
                                     + Fraction(1, 10 ** 6))
        tmp.write_text(json.dumps(tampered, ensure_ascii=False))
        try:
            ML.recompute_anchor_arm(tmp)
            detected = False
            detail = "未触发"
        except (SystemExit, AssertionError) as exc:
            detected = True
            detail = str(exc)[:120]
        check("⑤(a) 篡改 e_val(+1e-6) ⇒ 幂等重算逐位断言检出", detected, detail)
    # (b) 伪造 alive（e=E_ttp+1e-3）⇒ 合法性断言 exit 1（子进程）
    code = ("import sys; sys.path.insert(0, %r); sys.path.insert(0, %r); "
            "sys.path.insert(0, %r); from fractions import Fraction; "
            "from moment_lift import assert_arm_legality, E_TTP_TUBE; "
            "assert_arm_legality(Fraction(str(float(E_TTP_TUBE) + 1e-3)))"
            % (str(HERE), str(HERE / "typed"),
               str(HERE.parents[2] / "thomson-workflow" / "certificates")))
    proc = subprocess.run([sys.executable, "-c", code], capture_output=True,
                          text=True, timeout=300)
    check("⑤(b) 伪造 alive（e=E_ttp+1e-3）⇒ 合法性断言 exit 1",
          proc.returncode == 1, f"rc={proc.returncode} {proc.stdout[-120:]}")
    proc2 = subprocess.run(
        [sys.executable, "-c", code.replace("+ 1e-3", "- 1e-3")],
        capture_output=True, text=True, timeout=300)
    check("⑤(b) 对照：合法 e（E_ttp−1e-3）⇒ 合法性断言 exit 0",
          proc2.returncode == 0, f"rc={proc2.returncode}")
    # (c) 删锚定行重放 ⇒ 无锚定解的锚定残差必须被检出（|λ′(TTP)|>1e-9）
    hermite_sol = HERE / "results" / "hermite_cap_sol_m0748_M7.json"
    if not hermite_sol.exists():
        check("⑤(c) 无锚定对照解在档（hermite (7,6) cap sol）", False,
              f"缺失 {hermite_sol.name}")
        return
    sol = json.loads(hermite_sol.read_text())
    e_ = sol["exact"]
    qm, mm = ML.QuotientMaps(Fraction(-187, 250), 7, 6), None
    mm = ML.MomentMaps(qm)
    from hermite_ladder import pad_h
    h_AA = pad_h(ML.minorant_for(7)["coeffs"], qm.d_H)
    Gram, _z = ML.ttp_anchor_gram()
    ex = ML.AnchoredCapExporter(qm, mm, h_AA, h_AA, Gram, containers=False)
    data = dict(h_AA=list(h_AA), h_AB=list(h_AA),
                psi_AA=[Fraction(x) for x in e_["psi_AA"]],
                psi_AB=[Fraction(x) for x in e_["psi_AB"]],
                c_A=Fraction(e_["c_A"]), c_B=Fraction(e_["c_B"]),
                c_C=Fraction(e_["c_C"]), e=Fraction(e_["e"]),
                F=[[[Fraction(x) for x in row] for row in m_] for m_ in e_["F"]],
                G=[[[Fraction(0)] * mk for _ in range(mk)] for mk in mm.sizes],
                B={k2: [[Fraction(x) for x in row] for row in m_]
                   for k2, m_ in e_["B"].items()})
    rb = ML.anchored_readback(qm, mm, ex, data, Gram)
    detected = rb["lam_resid_maxrow"] > Fraction(1, 10 ** 9)
    check("⑤(c) 删锚定行重放（无锚定解）⇒ 锚定 λ 残差检出（>1e-9）",
          bool(detected),
          f"max|λ′(TTP)|={float(rb['lam_resid_maxrow']):.3e}（e="
          f"{float(data['e']):.12f}）")


# ============================================================ 主流程
def main() -> int:
    t0 = time.time()
    print(f"[gate] r8_anchor_gate 启动（seed {SEED}，python {sys.version.split()[0]}，"
          f"CWD={Path.cwd()}）", flush=True)
    if not ARCHIVE.exists():
        print(f"[gate] FAIL：账本缺失 {ARCHIVE}")
        return 1
    arch = json.loads(ARCHIVE.read_text())
    arms = ledger_checks(arch)
    if "A" in arms and "B" in arms:
        idempotence_checks(arms)
        verdict_checks(arch, arms)
        hygiene_checks(arms)
        negative_controls(arms)
    print("-" * 72, flush=True)
    print(f"[gate] 检查统计：{_checks['passed']} 过 / {_checks['failed']} 败"
          f"（{time.time() - t0:.0f}s，verdict={arch.get('verdict', {}).get('verdict')}）",
          flush=True)
    if _failures:
        for f in _failures:
            print(f"[gate:FAIL] {f}", flush=True)
        return 1
    print(f"[gate] exit 0 — 过门", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
