#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r7_capm9_gate.py — Round 7 / R7B cap m0748 M9 typed 验收门。

验收内容（任务书口径，seed 20261009，CWD 无关——路径全部自 __file__ 解析，
只验存档数据＋进程外 --verify-cert，不触发任何求解）：
  ① rung 行在盘（typed_ladder.json rungs[] 恰一 m0748 M=9 行）＋
     证书在盘（certificates/n9-stage-a4-typedcap-m0748_M9.json）＋
     解档在盘（results/typed_ladder_sol_m0748_M9.json）＋
     证书 params/provenance 记 --M 9/round_bits(∈--ks 48 56 64)/code_version；
  ② 进程外 typed_ladder.py --verify-cert exit 0（重建＋精确重算 certified）；
  ③ 铁律（精确 Fraction）：0 < certified ≤ E* + 1e-6；
  ④ 证书 claimed_bound == 行 certified（Fraction 精确相等）；
  ⑤ lift = certified − M8 基线（任务书固定精确分数）——只记录为数据，
     不断言符号（certified ≤ M8 时 rung 在盘、select_cap max 取界自动不选，
     零账面污染——D27 裁决 2/回滚点 ②；endgame 消费归 R7C）；
  ⑥ 解档一致性：solver_info.phase_value=="pdOPT"、iteration 为非负 int、
     solve_s 在档，与 rung 行 sdpa 字段逐项一致；cert provenance 的
     solution_sha256_16 与解档 exact 段重算一致；行 e_raw 与解档 exact.e
     换算一致；certified ≤ e_raw + 1e-9。
  负对照三件：
     NC1 /tmp 副本证书 claimed_bound + 1e-9 ⇒ --verify-cert exit ≠ 0；
     NC2 M8 冒充 M9（行 M=9 指向在盘 M8 证书、行 certified 同步冒充为 M8
         claimed_bound——唯一破绽即 params.M）⇒ 行校验必经证书 params.M 检出；
     NC3 /tmp 副本 ladder 的 M9 行指向不存在证书 ⇒ 行校验必拒。
用法：python3 thomson-n9/numerics/bounds/r7_capm9_gate.py   （任意 CWD）
exit 0 = 过门。
"""
from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
LADDER = HERE / "results" / "typed_ladder.json"
CERT_REL = "certificates/n9-stage-a4-typedcap-m0748_M9.json"
SOL_REL = "numerics/bounds/results/typed_ladder_sol_m0748_M9.json"
M8_CERT_REL = "certificates/n9-stage-a4-typedcap-m0748_M8.json"
WORKFLOW_DATA = HERE.parents[2] / "thomson-workflow" / "data" / "energies.json"

SEED = 20261009
E_TOL = Fr(1, 10 ** 6)
EPS9 = Fr(1, 10 ** 9)
KS = (48, 56, 64)
M9, K6 = 9, 6
A0 = Fr(-187, 250)
# 任务书 ⑤ 的 M8 精确基线（= typed_ladder.json m0748 M=8 行 certified）
M8_BASELINE = Fr("93712774192614269082019881043884635719865006109330352046526968479156494140625"
                 "/3637978812512164763811573465387274966467532527973356366318401998010742048629")

checks = []


def chk(name: str, ok: bool, detail: str = "") -> bool:
    checks.append((name, bool(ok), detail))
    print(f"[{'OK ' if ok else 'FAIL'}] {name}" + (f"：{detail}" if detail else ""),
          flush=True)
    return bool(ok)


def E_star() -> Fr:
    return Fr(str(json.loads(WORKFLOW_DATA.read_text())["energies"]["9"]["value"]))


def resolve(p: str) -> Path:
    q = Path(p)
    return q if q.is_absolute() else REPO / q


def run_verify_cert(cert_path: Path) -> tuple[int, str]:
    """进程外 typed_ladder.py --verify-cert（与任务书 ② 同一入口）。"""
    r = subprocess.run([sys.executable, str(HERE / "typed_ladder.py"),
                        "--verify-cert", str(cert_path)],
                       capture_output=True, text=True, timeout=1800)
    return r.returncode, (r.stdout[-300:] + r.stderr[-300:])


# ---------------------------------------------------------- 行级校验（可重入于篡改副本）
def validate_rung(db_path: Path, Estar: Fr) -> tuple[list[str], dict, dict | None]:
    """对 ladder db 的 m0748 M=9 行做全部行级校验；返回 (问题清单, 行, 证书 dict)。

    问题清单空 = 全过。db_path 可指向 /tmp 篡改副本（负对照用）。"""
    probs: list[str] = []
    row: dict = {}
    cert: dict | None = None
    if not db_path.exists():
        return [f"typed_ladder db 不在盘：{db_path}"], row, cert
    db = json.loads(db_path.read_text())
    rows9 = [r for r in db.get("rungs", [])
             if r.get("tag") == "m0748" and r.get("M") == M9]
    if len(rows9) != 1:
        return [f"m0748 M=9 行数 {len(rows9)} ≠ 1"], row, cert
    row = rows9[0]
    # 行自身字段
    if row.get("K") != K6:
        probs.append(f"行 K={row.get('K')} ≠ {K6}")
    try:
        if Fr(str(row.get("a0"))) != A0:
            probs.append(f"行 a0={row.get('a0')} ≠ −187/250")
    except Exception:
        probs.append(f"行 a0 非法：{row.get('a0')}")
    if row.get("certified") is None:
        probs.append("行缺 certified 精确分数")
        return probs, row, cert
    # 证书在盘 + params/provenance
    crel = row.get("certificate")
    cpath = resolve(crel) if crel else None
    if not crel or cpath is None or not cpath.exists():
        probs.append(f"rung 指向的证书不在盘（{crel}）")
        return probs, row, cert
    cert = json.loads(cpath.read_text())
    if cert.get("kind") != "n9-stage-a4-typedcap" or cert.get("tag") != "m0748":
        probs.append(f"证书 kind/tag 异常：{cert.get('kind')}/{cert.get('tag')}")
    prm = cert.get("params", {})
    if prm.get("M") != row.get("M"):
        probs.append(f"证书 params.M={prm.get('M')} ≠ 行 M={row.get('M')}"
                     f"（M8 冒充/张冠李戴检出）")
    if prm.get("K") != K6:
        probs.append(f"证书 params.K={prm.get('K')} ≠ {K6}")
    try:
        if Fr(str(prm.get("a0"))) != A0:
            probs.append(f"证书 params.a0={prm.get('a0')} ≠ −187/250")
    except Exception:
        probs.append(f"证书 params.a0 非法：{prm.get('a0')}")
    prov = cert.get("provenance", {})
    rb = prov.get("round_bits")
    if rb != row.get("round_bits"):
        probs.append(f"证书 provenance.round_bits={rb} ≠ 行 round_bits="
                     f"{row.get('round_bits')}")
    if rb not in KS:
        probs.append(f"round_bits={rb} 不在 --ks {list(KS)} 内")
    if not str(prov.get("code_version", "")):
        probs.append("证书 provenance.code_version 缺失")
    # ④ claimed_bound == 行 certified（Fraction 精确相等）
    cb = cert.get("claimed_bound")
    if cb is None or Fr(str(cb)) != Fr(str(row["certified"])):
        probs.append(f"证书 claimed_bound 与行 certified 失配（{cb} ≠ "
                     f"{row['certified']}）")
    # ③ 铁律（精确 Fraction）
    c = Fr(str(row["certified"]))
    if not (0 < c <= Estar + E_TOL):
        probs.append(f"铁律失败：0 < {float(c):.15e} ≤ E*+1e-6 不成立")
    # 解档在盘（行 solution 字段）
    srel = row.get("solution")
    if not srel or not resolve(srel).exists():
        probs.append(f"rung 指向的解档不在盘（{srel}）")
    # 行浮点换算自洽
    if row.get("certified_float") != float(c):
        probs.append("行 certified_float 与 certified 精确换算失配")
    return probs, row, cert


def validate_solution(row: dict, cert: dict) -> list[str]:
    """⑥ 解档 phase/iter/哈希一致性（读档核对，零求解）。"""
    probs: list[str] = []
    srel = row.get("solution")
    spath = resolve(srel) if srel else None
    if spath is None or not spath.exists():
        return [f"解档不在盘（{srel}）"]
    sol = json.loads(spath.read_text())
    if sol.get("tag") != "m0748" or sol.get("M") != M9 or sol.get("K") != K6:
        probs.append(f"解档 tag/M/K = {sol.get('tag')}/{sol.get('M')}/{sol.get('K')}"
                     f" ≠ m0748/{M9}/{K6}")
    try:
        if Fr(str(sol.get("a0"))) != A0:
            probs.append(f"解档 a0={sol.get('a0')} ≠ −187/250")
    except Exception:
        probs.append(f"解档 a0 非法：{sol.get('a0')}")
    si = sol.get("solver_info", {})
    if si.get("phase_value") != "pdOPT":
        probs.append(f"解档 phase_value={si.get('phase_value')} ≠ pdOPT")
    it = si.get("iteration")
    if not isinstance(it, int) or it < 0:
        probs.append(f"解档 iteration={it} 非非负 int")
    if not isinstance(si.get("solve_s"), (int, float)) or si.get("solve_s") is None:
        probs.append(f"解档 solve_s={si.get('solve_s')} 缺失/非数值")
    # 与 rung 行内嵌 sdpa（= 解档 solver_info 快照）逐项一致
    rs = row.get("sdpa", {})
    for key in ("phase_value", "iteration"):
        if rs.get(key) != si.get(key):
            probs.append(f"行 sdpa.{key}={rs.get(key)} ≠ 解档 {si.get(key)}")
    if isinstance(si.get("solve_s"), (int, float)) \
            and isinstance(rs.get("solve_s"), (int, float)) \
            and abs(rs["solve_s"] - si["solve_s"]) > 1e-6:
        probs.append(f"行 sdpa.solve_s={rs.get('solve_s')} ≠ 解档 {si.get('solve_s')}")
    # 证书 provenance.solver.sdpa（新鲜求解时应为完整 dict）与解档一致
    psd = (cert.get("provenance", {}).get("solver", {}) or {}).get("sdpa")
    if isinstance(psd, dict):
        if psd.get("phase_value") != si.get("phase_value"):
            probs.append("证书 provenance.solver.sdpa.phase_value 与解档失配")
        if psd.get("iteration") != si.get("iteration"):
            probs.append("证书 provenance.solver.sdpa.iteration 与解档失配")
    # solution_sha256_16 绑定：sha256(json.dumps(sol.exact, sort_keys=True))[:16]
    sha = hashlib.sha256(json.dumps(sol.get("exact", {}), sort_keys=True)
                         .encode()).hexdigest()[:16]
    want = cert.get("provenance", {}).get("solution_sha256_16")
    if sha != want:
        probs.append(f"解档 exact 段 sha256[:16]={sha} ≠ 证书 {want}")
    # 行 e_raw 与解档 exact.e 换算一致 + certified ≤ e_raw + 1e-9
    try:
        e_exact = Fr(str(sol["exact"]["e"]))
        if row.get("e_raw") != float(e_exact):
            probs.append("行 e_raw 与解档 exact.e 换算失配")
        if Fr(str(row["certified"])) > e_exact + EPS9:
            probs.append("行 certified > e_raw + 1e-9（不可能）")
    except Exception as exc:
        probs.append(f"解档 exact.e 解析失败：{exc}")
    return probs


def main() -> int:
    print(f"== R7B cap m0748 M9 typed 验收门（seed {SEED}）==", flush=True)
    Estar = E_star()
    for p in (LADDER, REPO / CERT_REL, REPO / SOL_REL):
        if not p.exists():
            print(f"[FAIL] 前置产物不在盘：{p}（负对照无从构造，门按未过处理）")
            return 1

    # ---------- ① rung/证书/解档在盘 + schema ----------
    probs, row, cert = validate_rung(LADDER, Estar)
    on_disk = (LADDER.exists() and (REPO / CERT_REL).exists() and (REPO / SOL_REL).exists())
    c_show = float(Fr(str(row.get("certified", "0"))))
    detail = (f"rung+证书+解档在盘；certified={c_show:.12f}"
              f"（round_bits={row.get('round_bits')}，"
              f"code_version={cert.get('provenance', {}).get('code_version') if cert else '?'}）"
              if (on_disk and not probs) else "；".join(probs[:6]))
    chk("G1_rung_cert_sol_on_disk_and_schema", on_disk and not probs, detail)

    # ---------- ② 进程外 --verify-cert ----------
    rc, out = run_verify_cert(REPO / CERT_REL)
    chk("G2_verify_cert_exit0", rc == 0,
        f"exit {rc}（{'重算一致 ✓' if rc == 0 else out[-200:]}）")

    # ---------- ④⑤（③ 已在 validate_rung；此处复核并记 lift 数据） ----------
    db = json.loads(LADDER.read_text())
    c9 = Fr(str(row.get("certified", "0")))
    # M8 基线双源核对：任务书固定分数 == 在盘 M8 rung certified
    m8_rows = [r for r in db.get("rungs", [])
               if r.get("tag") == "m0748" and r.get("M") == 8]
    m8_ok = bool(m8_rows) and Fr(str(m8_rows[0]["certified"])) == M8_BASELINE
    lift = c9 - M8_BASELINE
    verdict = ("lift>0 ⇒ select_cap 将换记 M9 证书" if lift > 0 else
               "lift≤0 ⇒ rung 在盘但 select_cap（max 取界）自动不选，零账面污染")
    chk("G4_claimed_bound_eq_row_certified",
        m8_ok and cert is not None
        and Fr(str(cert.get("claimed_bound"))) == c9,
        f"Fraction 精确相等；M8 基线任务书分数与在盘 M8 rung certified "
        f"{'一致' if m8_ok else '失配'}")
    chk("G5_lift_recorded_as_data", True,
        f"lift = certified − M8 = {lift}（float {float(lift):+.6e}）——数据记录，"
        f"不断言符号；{verdict}（消费归 R7C）")
    # ③ 铁律单列（与 ① 内联断言双保险，独立成门便于定位）
    chk("G3_iron_law_fraction", 0 < c9 <= Estar + E_TOL,
        f"0 < {float(c9):.15f} ≤ E*+1e-6 = {float(Estar + E_TOL):.9f} "
        f"（E* − certified = {float(Estar - c9):.9e}，精确 Fraction）")

    # ---------- ⑥ 解档一致性 ----------
    probs = validate_solution(row, cert or {})
    si_hint = ""
    try:
        sol = json.loads(resolve(row["solution"]).read_text())
        si = sol.get("solver_info", {})
        si_hint = (f"phase={si.get('phase_value')} iter={si.get('iteration')} "
                   f"solve_s={si.get('solve_s')}s")
    except Exception:
        si_hint = "解档读取失败"
    chk("G6_solution_phase_iter_consistency", not probs,
        f"{si_hint}；sha256 绑定一致" if not probs else "；".join(probs[:6]))

    # ---------- NC1：/tmp 副本证书 claimed_bound + 1e-9 ----------
    cj = json.loads((REPO / CERT_REL).read_text())
    cj["claimed_bound"] = str(Fr(cj["claimed_bound"]) + EPS9)
    with tempfile.NamedTemporaryFile(suffix=".json", delete=False,
                                     prefix="r7b_nc1_") as tf:
        tf.write(json.dumps(cj).encode())
        tcert = Path(tf.name)
    rc1, _out1 = run_verify_cert(tcert)
    chk("NC1_cert_claimed_bound_plus_1e-9_detected", rc1 != 0,
        f"--verify-cert exit {rc1}（{'检出' if rc1 != 0 else '未检出——负对照失败'}）")
    tcert.unlink(missing_ok=True)

    # ---------- NC2：M8 冒充 M9（行 M=9 指向在盘 M8 证书） ----------
    m8_cert = json.loads((REPO / M8_CERT_REL).read_text())
    tam_db = copy.deepcopy(db)
    row9 = next(r for r in tam_db["rungs"]
                if r.get("tag") == "m0748" and r.get("M") == M9)
    row9.update(certificate=M8_CERT_REL,
                certified=m8_cert["claimed_bound"],
                certified_float=float(Fr(m8_cert["claimed_bound"])))
    with tempfile.NamedTemporaryFile(suffix=".json", delete=False,
                                     prefix="r7b_nc2_") as tf:
        tf.write(json.dumps(tam_db).encode())
        tdb = Path(tf.name)
    probs, _r, _c = validate_rung(tdb, Estar)
    mflag = [p for p in probs if "params.M" in p]
    chk("NC2_m8_impersonation_detected_by_M_field", bool(mflag),
        ("检出：" + "；".join(mflag[:3])) if mflag else "未检出（负对照失败）")
    tdb.unlink(missing_ok=True)

    # ---------- NC3：rung 指向不存在证书 ⇒ 拒 ----------
    tam_db = copy.deepcopy(db)
    row9 = next(r for r in tam_db["rungs"]
                if r.get("tag") == "m0748" and r.get("M") == M9)
    row9["certificate"] = "certificates/n9-stage-a4-typedcap-m0748_M9_NONEXISTENT.json"
    with tempfile.NamedTemporaryFile(suffix=".json", delete=False,
                                     prefix="r7b_nc3_") as tf:
        tf.write(json.dumps(tam_db).encode())
        tdb = Path(tf.name)
    probs, _r, _c = validate_rung(tdb, Estar)
    nflag = [p for p in probs if "证书不在盘" in p]
    chk("NC3_rung_to_missing_cert_rejected", bool(nflag),
        ("拒：" + "；".join(nflag[:3])) if nflag else "未拒（负对照失败）")
    tdb.unlink(missing_ok=True)

    n_pass = sum(1 for _, ok, _ in checks if ok)
    print(f"== 门总计：{n_pass}/{len(checks)} 过 ==", flush=True)
    return 0 if n_pass == len(checks) else 1


if __name__ == "__main__":
    sys.exit(main())
