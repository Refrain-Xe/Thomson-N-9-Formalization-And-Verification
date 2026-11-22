#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r7_eps_chain_gate.py — Round 7 / R7-3 ε-链零件验收门（L3 nodeLocal 严格化 ＋ L6 斜率压缩）。

验收内容（任务书口径，seed 20261007，CWD 无关——路径全部自 __file__ 解析）：
  ① 两脚本幂等重算与存档逐位一致（l6_intube / l3_analytic 重跑 exit 0 且 json 不被重写）；
  ② 新层字段完整（l3.nodeLocal：C_glob 区间、分支统计、criterion、链 caliber (c)；
     l6.taylorDecomposition：K-lift 斜率、二阶通道、advisory 采样、新 r*）；
  ③ 负对照：W→10W/×100（ε_W 精确预测复核、余量 ~10× 退化、存档失配检出、×100 判据翻
     fail）、c0 冒充 C_glob 被一致性门拦、nodeLocal ε 单调性破坏检出、L6 四负对照全部触发；
  ④ 链判定字段按新常数刷新且与 l4.json / l6_intube.json / l2_rigorous.json 常数一致
     （gate 独立重算 ε* = C_glob_lo·ρ_target² 并核对 premise_ok/deficit_factor）。
另含 gate 级独立抽查（seed 20261007 ≠ 脚本内部 seed 20261006）：C_glob 的 float 稠密
重采样必须落入严格化区间。

【R8-3 口径注记（decisions D23）】l6_intube.json 已升 schema
thomson-n9/bounds/l6-intube/2（BD 二阶规则修复＋二阶提升通道 σ_max(J₂) 窗口积分）：
本门的 l6 幂等口径（①"archive check"行＋json 不重写）与字段口径（②
taylorDecomposition.firstOrder/secondOrder/advisorySpotChecks/appliesToBins/mechanism）
对 /2 存档继续成立（实测 17/17，2026-10-06 本会话亲跑）；r* 阈值（②
G2_l6_rstar_improved_not_worse ≥ 0.003359199152）仍以 R7-3 下界为地板，/2 的
r*=0.00950125 满足。L6 负对照口径（③ 四项）不变；/2 新增第 5 项
（channelSwapScalarDecoupledControl）由 r8_l6_gate.py 验收，本门不重复检查。
④ 的 ε* 重算随 r* 自动刷新（ε* ∝ r*²）。

用法：python3 thomson-n9/numerics/bounds/r7_eps_chain_gate.py   （任意 CWD）
exit 0 = 过门。
"""
from __future__ import annotations

import hashlib
import json
import math
import random
import subprocess
import sys
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
RESULTS = HERE / "results"
SEED = 20261007

L3_JSON = RESULTS / "l3_analytic.json"
L6_JSON = RESULTS / "l6_intube.json"
L4_JSON = RESULTS / "l4.json"
L2_JSON = RESULTS / "l2_rigorous.json"
PROBE_JSON = RESULTS / "hermite_probe.json"

checks = []


def chk(name: str, ok: bool, detail: str = "") -> bool:
    checks.append((name, bool(ok), detail))
    print(f"[{'OK ' if ok else 'FAIL'}] {name}" + (f"：{detail}" if detail else ""),
          flush=True)
    return bool(ok)


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main() -> int:
    print(f"== R7-3 ε-链零件验收门（seed {SEED}）==", flush=True)
    for p in (L3_JSON, L6_JSON, L4_JSON, L2_JSON, PROBE_JSON):
        if not p.exists():
            print(f"[FAIL] 缺输入 {p}")
            return 1
    h3_0, h6_0 = sha(L3_JSON), sha(L6_JSON)

    # ---------- ① 幂等重算（先 l6 再 l3：l3 的链 caliber 读 l6 的 r*） ----------
    r6 = subprocess.run([sys.executable, str(HERE / "l6_intube.py")],
                        capture_output=True, text=True, timeout=600)
    ok6 = r6.returncode == 0 and "archive check: recomputation identical" in r6.stdout
    chk("G1_l6_idempotent", ok6,
        f"exit={r6.returncode}；{'逐位一致' if ok6 else (r6.stdout[-200:] + r6.stderr[-200:])}")
    r3 = subprocess.run([sys.executable, str(HERE / "l3_analytic.py")],
                        capture_output=True, text=True, timeout=600)
    ok3 = r3.returncode == 0 and sha(L3_JSON) == h3_0 and sha(L6_JSON) == h6_0
    chk("G1_l3_idempotent_no_rewrite", ok3,
        f"exit={r3.returncode}；json 未重写={sha(L3_JSON) == h3_0 and sha(L6_JSON) == h6_0}")
    if not (ok6 and ok3):
        return 1

    l3 = json.loads(L3_JSON.read_text())
    l6 = json.loads(L6_JSON.read_text())
    l4 = json.loads(L4_JSON.read_text())
    l2 = json.loads(L2_JSON.read_text())
    nl = l3.get("nodeLocal", {})

    # ---------- ② 新层字段完整 ----------
    def frac(s):
        return Fr(str(s))

    c_ok = "C_glob" in nl and all(k in nl["C_glob"] for k in
                                  ("lo", "hi", "lo_float", "hi_float", "binding_cell"))
    c_lo, c_hi = (frac(nl["C_glob"]["lo"]), frac(nl["C_glob"]["hi"])) if c_ok else (Fr(0), Fr(0))
    chk("G2_l3_C_glob_fields", c_ok and 0 < c_lo <= c_hi,
        f"C_glob ∈ [{nl['C_glob'].get('lo_float'):.9e}, {nl['C_glob'].get('hi_float'):.9e}]"
        f"（宽 {float((c_hi - c_lo) / c_lo):.2e}，结合胞元 {nl['C_glob'].get('binding_cell')}）")
    bs = nl.get("branch_stats", {})
    chk("G2_l3_branch_stats", all(k in bs for k in
                                  ("taylor_pieces", "bb_evals", "bb_leaves", "bb_splits",
                                   "bb_maxdepth")) and (bs.get("bb_evals", 0) > 0),
        f"taylor_pieces={bs.get('taylor_pieces')} bb_evals={bs.get('bb_evals')} "
        f"bb_leaves={bs.get('bb_leaves')} splits={bs.get('bb_splits')} maxdepth={bs.get('bb_maxdepth')}")
    chk("G2_l3_criterion_fields",
        all(k in nl.get("criterion", {}) for k in
            ("threshold", "passed", "margin", "margin_float")) and
        all(k in nl.get("eps_W", {}) for k in ("lo", "hi", "hi_float", "archived_float")),
        f"判据 passed={nl.get('criterion', {}).get('passed')}，"
        f"margin={nl.get('criterion', {}).get('margin_float')}")
    ccx = nl.get("cross_checks", {})
    chk("G2_l3_crosschecks_all_ok",
        ccx.get("all_ok") is True and
        ccx.get("c0_two_paths_14digits") is True and
        ccx.get("taylor_vs_bb_overlap", {}).get("both_valid_lower") is True and
        ccx.get("float_dense_scan", {}).get("inside_certified_interval") is True,
        f"c0 14 位一致；Taylor/B&B 同区间双下界成立；float 稠密扫描 min="
        f"{ccx.get('float_dense_scan', {}).get('min'):.9e} 落入严格化区间")
    td = l6.get("taylorDecomposition", {})
    qg = l6.get("quadraticGrowth", {})
    r_star = frac(qg.get("rigorousRadius", "0"))
    _mu = qg["muAtRstar"]
    if isinstance(_mu, str):
        _mu = [s.strip() for s in _mu.strip("[]").split(",")]
    mu_lo = frac(_mu[0])
    chk("G2_l6_taylor_fields",
        all(k in td for k in ("firstOrder", "secondOrder", "advisorySpotChecks",
                              "appliesToBins", "mechanism")) and
        "klam_slope" in td.get("firstOrder", {}) and
        all(s.get("holds") for s in td.get("advisorySpotChecks", [])),
        f"K-lift 斜率={td.get('firstOrder', {}).get('klam_slope')}；"
        f"advisory 采样 {len(td.get('advisorySpotChecks', []))}/{len(td.get('advisorySpotChecks', []))} 成立")
    chk("G2_l6_rstar_improved_not_worse",
        r_star >= Fr("0.003359199152") and mu_lo > 0,
        f"r*={float(r_star):.10f}（旧 0.003359199152，{float(r_star / Fr('0.003359199152')):.2f}×），"
        f"μ 下端={float(mu_lo):.6e}（旧 0.0021869607）")

    # ---------- ③ 负对照 ----------
    ncs = l3.get("negative_controls", {})
    chk("G3_l3_NC4_width_x10", ncs.get("NC4_minorant_width_x10", {}).get("triggered") is True,
        f"ε_W 比 {ncs.get('NC4_minorant_width_x10', {}).get('eps_W_ratio_x10')}；"
        f"余量退化 {ncs.get('NC4_minorant_width_x10', {}).get('margin_degradation_factor')}×；"
        f"×100 判据 fail={ncs.get('NC4_minorant_width_x10', {}).get('x100_criterion_fails')}")
    chk("G3_l3_NC5_c0_impersonation",
        ncs.get("NC5_c0_impersonation", {}).get("triggered") is True,
        (ncs.get("NC5_c0_impersonation", {}).get("error") or "")[:80])
    chk("G3_l3_NC6_eps_monotone",
        ncs.get("NC6_nodelocal_eps_monotone", {}).get("triggered") is True)
    chk("G3_l3_legacy_NC123", all(ncs.get(k, {}).get("triggered") is True for k in
                                  ("NC1_C_times_10", "NC2_node_gap_halved",
                                   "NC3_eps_monotonicity")))
    nc6 = l6.get("negativeControls", {})
    chk("G3_l6_four_controls",
        all(nc6.get(k, {}).get("triggered") is True for k in
            ("doubleRadiusControl", "muSignFlipControl",
             "stressSignFlipControl", "stressWeightControl")),
        "加倍半径 / μ 符号翻转 / 应力符号翻转 / 应力权重篡改 全部触发")

    # ---------- ④ 链判定与常数一致性 ----------
    links = nl.get("chain_caliber_c", {}).get("links", {})
    have = all(k in links for k in ("L3_need", "L5", "L6"))
    delta_max = frac(l4["constants"]["delta_max_exact"])
    C_pro = frac(l4["constants"]["C_exact"])
    eps_forcing = frac(l2["eps_forcing"]["exact"])
    epsW_hi = frac(nl["eps_W"]["hi"])
    hg = frac(l3["inputs"]["half_gap"])
    okL = True
    det = []
    for nm, rho in (("L3_need", hg), ("L5", delta_max), ("L6", r_star / C_pro)):
        if not have:
            okL = False
            break
        lk = links[nm]
        eps_star = c_lo * rho * rho
        match = abs(frac(lk["eps_star"]) - eps_star) <= abs(eps_star) * Fr(1, 10 ** 30) + Fr(1, 10 ** 40)
        prem = (eps_star >= epsW_hi) == bool(lk["premise_ok"])
        okL = okL and match and prem
        det.append(f"{nm}: ε*={float(eps_star):.3e} {'过' if lk['premise_ok'] else '缺口'}"
                   f"{lk.get('margin_float') if lk['premise_ok'] else lk.get('deficit_factor_float'):.2f}×"
                   f"（常数{'一致' if match else '失配'}）")
    chk("G4_chain_links_consistent", okL, "；".join(det))
    chk("G4_chain_inputs_match_archives",
        frac(l3["inputs"]["delta_max"]["exact"]) == delta_max and
        frac(l3["inputs"]["C_procrustes"]["exact"]) == C_pro and
        frac(l3["inputs"]["eps_forcing"]["exact"]) == eps_forcing and
        frac(nl["r_star_l6_used"]["value"]) == r_star,
        "δ_max/C_pro ↔ l4.json；ε_forcing ↔ l2_rigorous.json；r* ↔ l6_intube.json")
    caliber_a = nl.get("chain_caliber_c", {}).get("caliber_a_rerun", {})
    chk("G4_caliber_a_honest_fail",
        caliber_a.get("thresholds_met") is False and caliber_a.get("vacuous") is True,
        f"口径(a) ε_forcing={float(eps_forcing):.4e} 下 ρ_raw={caliber_a.get('rho_raw_float')}"
        f"（vacuous ⇒ 链 fail——cap 未抬前不闭合，如实）")

    # ---------- gate 级独立抽查（seed 20261007） ----------
    nodes = [Fr(str(v)) for v in l3["inputs"]["nodes"]]
    ns = sorted(nodes)
    bnds = [Fr(-1)] + [(ns[i] + ns[i + 1]) / 2 for i in range(len(ns) - 1)] + [Fr(1)]
    coeffs = [Fr(s) for s in json.loads(PROBE_JSON.read_text())
              ["rigorous_minorant"]["coeffs"]]
    rng = random.Random(SEED)
    worst = float("inf")
    for k, nu in enumerate(ns):
        a, b = float(bnds[k]), min(float(bnds[k + 1]), 0.9995)
        for _ in range(3000):
            t = a + (b - a) * rng.random()
            dd = t - float(nu)
            if dd == 0:
                continue
            acc = 0.0
            for c in reversed(coeffs):
                acc = acc * t + float(c)
            worst = min(worst, (1.0 / math.sqrt(2.0 - 2.0 * t) - acc) / (dd * dd))
    inside = float(c_lo) * (1 - 1e-3) <= worst <= float(c_hi) * (1 + 1e-3)
    chk("Gx_independent_resample_seed_20261007", inside,
        f"独立 18000 点重采样 min ratio = {worst:.9e} ∈ "
        f"[{float(c_lo):.9e}, {float(c_hi):.9e}]")

    n_pass = sum(1 for _, ok, _ in checks if ok)
    print(f"== 门总计：{n_pass}/{len(checks)} 过 ==", flush=True)
    return 0 if n_pass == len(checks) else 1


if __name__ == "__main__":
    sys.exit(main())
