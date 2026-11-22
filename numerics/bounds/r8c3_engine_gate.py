#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r8c3_engine_gate.py — R8B engine-v2-strip 验收门（G1–G7 ＋ 负对照 NC1–NC3）.

任务书口径（D29 裁决 2/5/6）：KLT 式 minorant 引擎 v2（contact/triple）条件阶梯
重解 L0 洞片 [−153/200,−187/250] 的账本完整性、区间证书独立复算、分支断言、
预算门、事件流完整性、幂等重装配与 D31 留痕。固定种子 20261010；负对照全触发。

用法（thomson-n9 下）：
  python3 numerics/bounds/r8c3_engine_gate.py             # 全门（exit 0 = 过）
  python3 numerics/bounds/r8c3_engine_gate.py --assemble  # 幂等重装配 campaign 账本
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import subprocess
import sys
import tempfile
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "typed"))
sys.path.insert(0, str(REPO.parent / "thomson-workflow" / "certificates"))

SEED_GATE = 20261010
E_STAR_DEC = Fraction("25.759986531")          # 十进制精确口径（D28 裁决 3）
E_PLUS_TOL = Fraction(1, 10 ** 6)
EQUIV_UNIT_S = 10800
BUDGET_CAP_EQUIV = Fraction(93, 10)            # 9.30 当量
X9_THRESHOLD = Fraction("5.3e-5")              # = 53/1000000（十进制精确）
PHASE1_ACTUAL_CAP_S = 32400
PHASE2_KILL_S = 68000
TOTAL_CAP_S = 100400
CERTIFIED_A5_M9 = Fraction("725074535887477029/28147497671065600")   # 25.759822217973642
A5_M8_BASE = Fraction("7250644412926184559/281474976710656000")      # 25.759463585921285
A5_M10_BASE = Fraction("7250781808668634923/281474976710656000")     # 25.759951713654896
STRIP_LO = Fraction(-153, 200)
STRIP_HI = Fraction(-187, 250)

CAMPAIGN = RESULTS / "hermite_v2_campaign.json"
STATE = RESULTS / "hermite_v2_campaign_state.json"
PROBES = {"contact": RESULTS / "hermite_v2_probe_contact.json",
          "triple": RESULTS / "hermite_v2_probe_triple.json"}
SMOKE = RESULTS / "hermite_v2_smoke.json"
STRIPS_V2 = RESULTS / "hermite_v2_strips.json"
EVENTS = RESULTS / "r8c3_engine_solver_events.json"
HERMITE_STRIPS = RESULTS / "hermite_strips.json"
DECISIONS = REPO / "notes" / "decisions.md"
F0 = Fraction(0)


def fail(msg: str) -> None:
    print(f"[gate][FAIL] {msg}", flush=True)
    sys.exit(1)


def okmsg(msg: str) -> None:
    print(f"[gate][ok] {msg}", flush=True)


def jload(p: Path):
    return json.loads(p.read_text())


# ============================================================ 独立 Fraction/区间路径（G2 用，自写）
def _falling(j: int, m: int) -> int:
    if j < m:
        return 0
    out = 1
    for i in range(j - m + 1, j + 1):
        out *= i
    return out


def _dfact_odd(m: int) -> int:
    out = 1
    for i in range(1, 2 * m, 2):
        out *= i
    return out


def _tpow(a: Fraction, b: Fraction, j: int):
    if j == 0:
        return (Fraction(1), Fraction(1))
    if a >= 0:
        return (a ** j, b ** j)
    if b <= 0:
        return (b ** j, a ** j) if j % 2 == 1 else (F0, max(a ** j, b ** j))
    return (a ** j, b ** j) if j % 2 == 1 else (F0, max(a ** j, b ** j))


def gpoly_interval(coeffs, a: Fraction, b: Fraction):
    lo = hi = F0
    for j, c in enumerate(coeffs):
        if c == 0:
            continue
        plo, phi_ = _tpow(a, b, j)
        lo += min(c * plo, c * phi_)
        hi += max(c * plo, c * phi_)
    return (lo, hi)


def gsqrt_recip_interval(q: Fraction, B: int, power: int):
    """区间 ∋ q^{−power/2}（q>0 有理，power 奇正）。自写 isqrt 路径。"""
    Qn, Qd = q.numerator, q.denominator
    num, den = Qd ** power, Qn ** power
    Q = (num << (4 * B)) // den
    P = math.isqrt(Q)
    return (Fraction(P, 1 << (2 * B)), Fraction(P + 1, 1 << (2 * B)))


def gderiv(coeffs, m: int, t: Fraction) -> Fraction:
    acc = F0
    for j, c in enumerate(coeffs):
        if j >= m and c:
            acc += Fraction(_falling(j, m)) * c * t ** (j - m)
    return acc


def gpi_polynomial(nu_list, mult: int, cm: int):
    poly = [Fraction(1)]

    def mul(p, q):
        out = [F0] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            if a:
                for j2, b in enumerate(q):
                    out[i + j2] += a * b
        return out

    for v in nu_list:
        r = [Fraction(v)]
        for _ in range(mult - 1):
            r = mul(r, [Fraction(v)])
        poly = mul(poly, r)
    for _ in range(cm):
        poly = mul(poly, [Fraction(1), Fraction(1)])
    return poly


def gverify_probe(probe: dict) -> dict:
    """G2：变体 dyadic 构造＋区间证书＋占优的独立复算（只读 probe JSON 与
    tube.json，全部自写 Fraction/区间路径，不复用 hermite_minorant 代码）。"""
    tube = jload(RESULTS / "tube.json")["ttp_spectrum"]
    nodes_f = [float(x) for x in tube["nodes"]]
    nu = [Fraction(x) for x in nodes_f]
    cfg = probe["variant_config"]
    orders = [int(m) for m in cfg["orders"]]
    cm = int(cfg["contact_minus1"])
    k = int(probe["k"])
    W = Fraction(probe["W"])
    coeffs = [Fraction(s) for s in probe["coeffs"]]
    hw = [Fraction(s) for s in probe["halfwidths"]]
    checks = dict(variant=probe["variant"], sub={})

    # (a) W == Σ halfwidths
    checks["sub"]["W_eq_sum_hw"] = (W == sum(hw, F0))

    # (b) 逐节点逐阶插值条件（残差 ≤ 构造 slack：Σ_j hw_j·|(j)_m ν^{j−m}|；
    #     m=0 时常数项折叠的 −W 已在 coeffs 内；H^{(m)}(ν)=φ^{(m)}(ν) 精确）
    node_checks = []
    for v in nu:
        q = Fraction(2) - 2 * v
        for m in orders:
            iv = gsqrt_recip_interval(q, 200, 2 * m + 1)
            if m:
                pref = Fraction(_dfact_odd(m))
                iv = (pref * iv[0], pref * iv[1])
            mv = gderiv(coeffs, m, v)
            slack = sum(h * Fraction(abs(_falling(j, m)) * abs(v) ** (j - m))
                        for j, h in enumerate(hw) if j >= m)
            if m == 0:
                slack += W
            mid = (iv[0] + iv[1]) / 2
            good = abs(mv - mid) <= slack + (iv[1] - iv[0])
            node_checks.append(dict(node=str(v), order=m, val=str(mv),
                                    slack=str(slack), ok=bool(good)))
    checks["sub"]["interpolation_conditions"] = node_checks
    # (c) −1 接触行（contact）
    if cm:
        cmc = []
        for m in range(cm):
            mv = gderiv(coeffs, m, Fraction(-1))
            tgt = Fraction(_dfact_odd(m), 2 ** (2 * m + 1))
            slack = sum(h * Fraction(_falling(j, m)) for j, h in enumerate(hw)
                        if j >= m) + (W if m == 0 else 0)
            cmc.append(dict(order=m, val=str(mv), target=str(tgt),
                            slack=str(slack), ok=bool(abs(mv - tgt) <= slack)))
        checks["sub"]["contact_minus1_rows"] = cmc

    # (d) 区间证书逐区域复算（与探针同一数学、独立实现；Fraction 逐位比对）
    ncond = int(probe["ncond"])
    mult = len(orders)
    Pi = gpi_polynomial([Fraction(x) for x in nodes_f], mult, cm)
    c_const = Fraction(_dfact_odd(ncond), math.factorial(ncond))
    nu_sorted = sorted(nu)
    hull_right = nu_sorted[-1]
    breaks = sorted(set([Fraction(-1)] + nu + [Fraction(1)]))
    regions = []
    for a, b in zip(breaks[:-1], breaks[1:]):
        neg = sum(1 for v in nu if b <= v)
        pi_nonneg = (cm > 0) or (mult % 2 == 0) or (neg % 2 == 0)
        if pi_nonneg:
            regions.append(dict(interval=[str(a), str(b)], kind="theorem"))
            continue
        plo = None
        for i in range(512):
            x0 = a + (b - a) * Fraction(i, 512)
            x1 = a + (b - a) * Fraction(i + 1, 512)
            lo, _ = gpoly_interval(Pi, x0, x1)
            plo = lo if plo is None else min(plo, lo)
        rho = max(abs(a), abs(b))
        eps_lb = W - sum(h * rho ** j for j, h in enumerate(hw))
        q_hi = Fraction(2) - 2 * hull_right
        c_hi = c_const * gsqrt_recip_interval(q_hi, 200, 2 * ncond + 1)[1]
        bound = c_hi * plo + eps_lb
        regions.append(dict(interval=[str(a), str(b)], kind="composite",
                            bound=str(bound), ok=bool(bound >= 0)))
    checks["sub"]["certificate_regions"] = regions
    arch = probe["interval_certificate"]["regions"]
    same = len(arch) == len(regions)
    if same:
        for x, y in zip(arch, regions):
            if x.get("pi_sign", ">=0") != (">=0" if y["kind"] == "theorem" else "<0"):
                same = False
                break
            if y["kind"] == "composite" and Fraction(x["bound"]) != Fraction(y["bound"]):
                same = False
                break
    checks["sub"]["certificate_regions_match_archive"] = bool(same)
    checks["cert_ok_recomputed"] = all(r.get("ok", True) for r in regions)

    # (e) 占优独立复算（8193 点精确 dyadic 格；一致性单向断言）
    old_probe = PROBES.get("contact")
    dy_old_coeffs = None
    # M_old＝现行 12 条 deg-11（k=48）：从 tube 独立重排（值+一阶导）
    n_old = 12
    rows, bmid = [], []
    for v in nu:
        q = Fraction(2) - 2 * v
        rows.append([v ** j for j in range(n_old)])
        iv = gsqrt_recip_interval(q, 200, 1)
        bmid.append((iv[0] + iv[1]) / 2)
        rows.append([Fraction(_falling(j, 1)) * v ** (j - 1) if j >= 1 else F0
                     for j in range(n_old)])
        iv2 = gsqrt_recip_interval(q, 200, 3)
        bmid.append((iv2[0] + iv2[1]) / 2)
    # 高斯消元（自写）
    Mx = [row[:] + [bmid[i]] for i, row in enumerate(rows)]
    for col in range(n_old):
        piv = next(r for r in range(col, n_old) if Mx[r][col] != 0)
        Mx[col], Mx[piv] = Mx[piv], Mx[col]
        pv = Mx[col][col]
        Mx[col] = [x / pv for x in Mx[col]]
        for r in range(n_old):
            if r != col and Mx[r][col]:
                f = Mx[r][col]
                Mx[r] = [x - f * y for x, y in zip(Mx[r], Mx[col])]
    hold = [Mx[i][n_old] for i in range(n_old)]
    # M_old 的 dyadic 舍入中点＝H_old 的 2^-48 最近格点（与探针一致口径：
    # 中点＝区间中点 dyadic 化；此处用 H 精确中点的最近 dyadic——差异 ≤ 2^-49·12
    # 不影响一致性断言的 1e-9 容差）

    def dyad_round(x, kk):
        return Fraction(round(x * (1 << kk)), 1 << kk)

    dy_old_coeffs = [dyad_round(x, 48) for x in hold]
    dy_old_coeffs[0] -= Fraction(12, 1 << 49)  # W_old 名义偏移（容差内一致性）

    grid_min = None
    nlen = max(len(coeffs), len(dy_old_coeffs))
    for i in range(8193):
        t = Fraction(-1) + Fraction(2 * i, 8192)
        d = sum((coeffs[j] if j < len(coeffs) else F0) * t ** j
                - (dy_old_coeffs[j] if j < len(dy_old_coeffs) else F0) * t ** j
                for j in range(nlen))
        grid_min = d if grid_min is None else min(grid_min, d)
    dom = probe["dominance_vs_old"]
    cons = []
    if grid_min < Fraction(-1, 10 ** 12):       # 容差内近似 M_old 重构（≤1e-14 级）
        cons.append(("negative_grid_implies_not_dominates",
                     not dom["dominates"]))
    if dom.get("certified"):
        cons.append(("certified_implies_dominates", bool(dom["dominates"])))
    cons.append(("archive_min_not_above_grid",
                 float(dom["min_float"]) <= float(grid_min) + 1e-9))
    checks["dominance_grid_min"] = str(grid_min)
    checks["dominance_consistency"] = [list(c) for c in cons]

    checks["ok"] = bool(checks["sub"]["W_eq_sum_hw"]
                        and all(c["ok"] for c in node_checks)
                        and all(c["ok"] for c in checks["sub"].get(
                            "contact_minus1_rows", [dict(ok=True)]))
                        and checks["sub"]["certificate_regions_match_archive"]
                        and all(v[1] for v in cons)
                        and checks["cert_ok_recomputed"]
                        == probe["interval_certificate"]["ok"])
    return checks


# ============================================================ 幂等装配（G6）
def _a5_baseline(tag: str, field: str = "certified"):
    db = jload(HERMITE_STRIPS)
    for r in db["strips"]:
        if r["tag"] == tag:
            return r[field]
    return None


def assemble_campaign() -> dict:
    """确定性装配 results/hermite_v2_campaign.json（只读在盘事实，零时钟）。"""
    st = jload(STATE)
    probes = {v: jload(p) for v, p in PROBES.items()}
    smoke = jload(SMOKE)
    ev = jload(EVENTS)
    strips_v2 = jload(STRIPS_V2) if STRIPS_V2.exists() else {"strips": []}
    rows = {(r.get("variant", "hermite"), r["M"]): r for r in strips_v2["strips"]}

    def rowsum(v, M):
        return rows.get((v, M))

    p1r = rowsum("contact", 9)
    p2r = rowsum("contact", 10) or rowsum("triple", 10)
    p1 = dict(st["phase1"])
    if p1r is not None:
        p1 = {**p1, "status": p1r["status"],
              "certified": p1r["certified"],
              "certified_float": p1r["certified_float"],
              "solve_s": (st["phase1"].get("solve_s")
                          if st["phase1"].get("solve_s") is not None
                          else p1r.get("sdpa", {}).get("solve_s")),
              "row_file": "results/hermite_v2_strips.json",
              "flips_decimal_E_star": bool(p1r.get("flips_decimal_E_star", False)),
              "margin_over_E_star_dec": p1r.get("margin_over_E_star_dec")}
        p1["outcome"] = ("certified" if p1r["status"] == "certified" else "blocked")
    X9 = None
    if p1.get("certified"):
        att = Fraction(p1["certified"])
        X9 = dict(value=str(att - CERTIFIED_A5_M9),
                  float=float(att - CERTIFIED_A5_M9),
                  ge_threshold=bool(att - CERTIFIED_A5_M9 >= X9_THRESHOLD),
                  threshold=str(X9_THRESHOLD),
                  definition="attempt_v2(M9) − certified_a5(M9)（十进制口径精确 Fraction）")
    p2 = dict(st["phase2"])
    trigger = None
    if p1.get("solve_s") is not None:
        s1 = Fraction(p1["solve_s"])
        cond = dict(
            X9_ge_threshold=bool(X9 and X9["ge_threshold"]),
            phase1_actual_le_32400=bool(s1 <= PHASE1_ACTUAL_CAP_S),
            budget_headroom=bool(s1 + PHASE2_KILL_S <= TOTAL_CAP_S),
            solve_s_actual=str(s1))
        cond["all"] = bool(cond["X9_ge_threshold"]
                           and cond["phase1_actual_le_32400"]
                           and cond["budget_headroom"])
        trigger = cond
    if p2r is not None:
        p2 = {**p2, "launched": True, "outcome": p2r["status"],
              "certified": p2r["certified"],
              "certified_float": p2r["certified_float"],
              "solve_s": (st["phase2"].get("solve_s")
                          if st["phase2"].get("solve_s") is not None
                          else p2r.get("sdpa", {}).get("solve_s")),
              "variant": p2r.get("variant")}
        X10 = dict(value=str(Fraction(p2r["certified"]) - A5_M10_BASE),
                   float=float(Fraction(p2r["certified"]) - A5_M10_BASE),
                   definition="attempt_v2(M10) − attempt_a5(M10)（十进制精确）")
    else:
        X10 = None
    if trigger is not None:
        p2["trigger_eval"] = trigger

    def pdict(v):
        p = probes[v]
        return dict(
            variant=v, k=p["k"], W=p["W"], W_float=p["W_float"],
            ncond=p["ncond"], remainder=p["remainder"],
            orders=p["variant_config"]["orders"],
            contact_minus1=p["variant_config"]["contact_minus1"],
            degree=p["variant_config"]["degree"], min_M=p["variant_config"]["min_M"],
            interval_certificate_ok=p["interval_certificate"]["ok"],
            interval_certificate_regions=[
                dict(interval=r["interval"], pi_sign=r.get("pi_sign", ">=0"),
                     bound=r.get("bound", "0")) for r in
                p["interval_certificate"]["regions"]],
            dominance_vs_old=dict(dominates=p["dominance_vs_old"]["dominates"],
                                  certified=p["dominance_vs_old"]["certified"],
                                  min_float=p["dominance_vs_old"]["min_float"]),
            strip_gap_ub=p["gap_metrics"]["strip"]["exact_grid_max_gap_ub"],
            strip_gap_ub_float=p["gap_metrics"]["strip"]
            ["exact_grid_max_gap_ub_float"],
            hull_gap_ub=p["gap_metrics"]["hull"]["exact_grid_max_gap_ub"],
            hull_gap_ub_float=p["gap_metrics"]["hull"]
            ["exact_grid_max_gap_ub_float"],
            dense_min=p["dense_and_local"]["dense"]["min"],
            local_min=p["dense_and_local"]["local"]["min"],
            c0_sq_gap=p["dense_and_local"]["ii_sq_gap"]["c0_dense"],
            e_anchor_deficit=p["e_anchor"]["deficit_ub"],
            probe_file=f"results/hermite_v2_probe_{v}.json")

    # slope 行（D22 裁决 4② schema，v2 视角）
    slope = []
    if p1.get("certified"):
        v9 = Fraction(p1["certified"])
        base8, base9, base10 = A5_M8_BASE, CERTIFIED_A5_M9, A5_M10_BASE
        row = dict(
            piece="m765-m748", engine="a5-hermite-v2-contact",
            M8=str(base8), M8_float=float(base8),
            M9=str(v9), M9_float=float(v9),
            M10=(str(Fraction(p2r["certified"])) if p2r is not None else None),
            M10_float=(float(Fraction(p2r["certified"])) if p2r is not None
                       else None),
            baseline_a5=dict(M8=str(base8), M9=str(base9), M10=str(base10),
                             M9_float=float(base9), M10_float=float(base10)),
            lift_M8_M9=dict(value=str(v9 - base8), float=float(v9 - base8)),
            lift_M9_M10=(dict(value=str(Fraction(p2r["certified"]) - v9),
                              float=float(Fraction(p2r["certified"]) - v9))
                         if p2r is not None else None),
            required_lift_M9_M10=dict(value=str(E_STAR_DEC - v9),
                                      float=float(E_STAR_DEC - v9)),
            X9=X9, X10=X10,
            sources=dict(
                M8="results/hermite_strips.json（a5 M8 行，精确分数）",
                M9="results/hermite_v2_strips.json（v2 contact M9 行 certified）",
                baseline_a5_M9="results/hermite_strips.json（a5 M9 行）",
                baseline_a5_M10="results/hermite_strips.json（a5 M10 行）"),
            verdict=p1["outcome"])
        if p2r is not None:
            row["retention_ratio"] = float(
                (Fraction(p2r["certified"]) - v9) / (v9 - base8))
        row["required_retention_ratio"] = float(
            (E_STAR_DEC - v9) / (v9 - base8))
        slope.append(row)

    solve_s_total = 0.0
    for ph in (p1, p2):
        if ph.get("solve_s") is not None:
            solve_s_total += ph["solve_s"]
    camp = dict(
        kind="hermite-v2-strip-campaign",
        campaign=st["campaign"],
        seed=st["seed"],
        E_star_decimal="25.759986531",
        E_star_decimal_fraction=str(E_STAR_DEC),
        EQUIV_UNIT_S=EQUIV_UNIT_S,
        budget_cap_equiv=float(BUDGET_CAP_EQUIV),
        phase0=dict(
            death_verdict=st["phase0"]["death_verdict"],
            death_rule=st["phase0"]["death_rule"],
            death_basis=st["phase0"]["death_basis"],
            selection_rule_predeclared=st["phase0"]["selection_rule_predeclared"],
            probe_files=st["phase0"]["probe_files"],
            smoke_file=st["phase0"]["smoke_file"],
            selection=st["phase0"]["selection"],
            zero_solve_declaration=st["phase0"]["zero_solve_declaration"],
            variants={v: pdict(v) for v in ("contact", "triple")},
            smoke=dict(fits_contact=smoke["fits_contact"],
                       fits_triple=smoke["fits_triple"],
                       structure=smoke["structure"],
                       rss_recheck_basis=smoke["rss_recheck"]["basis"]),
            strip_zone=[str(STRIP_LO), str(STRIP_HI)]),
        phase1=p1,
        phase2=p2,
        X9=X9,
        X10=X10,
        slope_rows=slope,
        solver_events_file="results/r8c3_engine_solver_events.json",
        budget=dict(solve_s_total=solve_s_total,
                    equiv=solve_s_total / EQUIV_UNIT_S,
                    cap_equiv=float(BUDGET_CAP_EQUIV), unit_s=EQUIV_UNIT_S),
        provenance=dict(
            assembler="numerics/bounds/r8c3_engine_gate.py::assemble_campaign",
            deterministic=True,
            inputs=[str(p.relative_to(REPO)) for p in
                    (STATE,) + tuple(PROBES.values()) + (SMOKE, STRIPS_V2,
                                                         EVENTS)]))
    return camp


# ============================================================ G4 规则（负对照可复用）
def check_budget(camp: dict):
    b = camp["budget"]
    unit = b["unit_s"]
    if unit != EQUIV_UNIT_S or camp["EQUIV_UNIT_S"] != EQUIV_UNIT_S:
        return False, f"EQUIV_UNIT_S 不一致：{unit}/{camp['EQUIV_UNIT_S']} ≠ 10800"
    tot = Fraction(b["solve_s_total"])
    if tot / EQUIV_UNIT_S > BUDGET_CAP_EQUIV:
        return False, (f"Σsolve_s={float(tot)}s = {float(tot / EQUIV_UNIT_S)}"
                       f" 当量 > 9.30 上限")
    # 分量一致性：phase1+phase2 solve_s 之和 == 总额
    parts = sum(Fraction(ph["solve_s"]) for ph in (camp["phase1"], camp["phase2"])
                if ph.get("solve_s") is not None)
    if parts != tot:
        return False, f"分量和 {float(parts)} ≠ 总额 {float(tot)}"
    return True, f"Σsolve_s={float(tot)}s={float(tot / EQUIV_UNIT_S)} 当量 ≤ 9.30"


def check_phase2_rule(camp: dict):
    """相位 2 触发三合一复核（X9 十进制精确比较）。返回 (ok, msg)。"""
    p2 = camp["phase2"]
    if not p2.get("launched"):
        return True, "相位 2 未启动（触发条件不满足，如实）"
    te = p2.get("trigger_eval")
    if not te:
        return False, "相位 2 已启动但 trigger_eval 缺失"
    X9 = camp.get("X9")
    if X9 is None:
        return False, "相位 2 已启动但 X9 缺失"
    # 独立重算三条件（十进制口径精确）
    att = Fraction(camp["phase1"]["certified"])
    x9 = att - CERTIFIED_A5_M9
    s1 = Fraction(camp["phase1"]["solve_s"])
    c1 = x9 >= X9_THRESHOLD
    c2 = s1 <= PHASE1_ACTUAL_CAP_S
    c3 = s1 + PHASE2_KILL_S <= TOTAL_CAP_S
    if not (c1 and c2 and c3):
        return False, (f"相位 2 启动违规：X9={float(x9):.3e} ≥阈={c1}，"
                       f"实耗={float(s1)} ≤32400={c2}，实耗+68000≤100400={c3}")
    if Fraction(te["solve_s_actual"]) != s1:
        return False, "trigger_eval.solve_s_actual 与 phase1.solve_s 不一致"
    return True, (f"相位 2 触发三合一复核通过（X9={float(x9):.3e} ≥ 5.3e-5；"
                  f"实耗 {float(s1)}s ≤ 32400；+68000 ≤ 100400）")


# ============================================================ 门体
def run_gate() -> None:
    rng_seed_used = SEED_GATE
    print(f"[gate] R8B engine-v2-strip 验收门（seed {rng_seed_used}）", flush=True)
    if not CAMPAIGN.exists():
        fail(f"账本不存在：{CAMPAIGN}（先 --assemble）")
    camp = jload(CAMPAIGN)

    # ---- G1 schema ----
    need = ["kind", "seed", "E_star_decimal", "EQUIV_UNIT_S", "phase0", "phase1",
            "phase2", "X9", "slope_rows", "solver_events_file", "budget",
            "provenance"]
    missing = [f for f in need if f not in camp]
    if missing:
        fail(f"G1 账本缺字段：{missing}")
    if camp["kind"] != "hermite-v2-strip-campaign" or camp["seed"] != SEED_GATE \
            or camp["E_star_decimal"] != "25.759986531":
        fail("G1 kind/seed/E* 十进制口径不符")
    ph0 = camp["phase0"]
    for f in ("death_verdict", "selection", "variants", "smoke",
              "selection_rule_predeclared"):
        if f not in ph0:
            fail(f"G1 phase0 缺 {f}")
    for v in ("contact", "triple"):
        pv = ph0["variants"][v]
        if pv["ncond"] not in (17, 18) or "orders" not in pv:
            fail(f"G1 变体 {v} 参数不完整")
    if not camp["slope_rows"]:
        fail("G1 slope 行缺失")
    okmsg("G1 账本 schema 完整（kind/seed/E* 十进制/变体参数/相位 0 判据/"
          "相位事件流/slope 行）")

    # ---- G2 独立复算 ----
    for v in ("contact", "triple"):
        res = gverify_probe(jload(PROBES[v]))
        if not res["ok"]:
            fail(f"G2 {v} 独立复算失败：{json.dumps(res)[:800]}")
        okmsg(f"G2 {v} 区间证书＋插值条件＋占优一致性独立复算通过"
              f"（证书={'过' if res['cert_ok_recomputed'] else '败'}，"
              f"占优格点 min={float(Fraction(res['dominance_grid_min'])):.3e}）")
        # 与账本 phase0 摘要一致
        if res["cert_ok_recomputed"] != camp["phase0"]["variants"][v][
                "interval_certificate_ok"]:
            fail(f"G2 {v} 证书判定与账本不一致")

    # ---- G3 分支断言 ----
    p1 = camp["phase1"]
    if ph0["death_verdict"]:
        if p1.get("outcome") is not None:
            fail("G3 探针判死分支：相位 1 不应有结局")
        if ph0.get("zero_solve_declaration") is None:
            fail("G3 探针判死分支：零求解声明缺失")
        okmsg("G3 探针判死分支：判死数据＋零求解声明在档")
    elif p1.get("outcome") in ("certified", "blocked"):
        # strips DB 交叉核对（账本行 vs hermite_v2_strips.json 引擎行）
        if STRIPS_V2.exists():
            sv = jload(STRIPS_V2)
            row9 = next((r for r in sv["strips"]
                         if r.get("variant") == "contact" and r["M"] == 9), None)
            if row9 is None or row9["certified"] != p1.get("certified"):
                fail("G3 v2 strips DB contact@M9 行与账本不逐位一致")
        if p1.get("outcome") == "certified":
            cands = ["certificates/n9-stage-a5v2-strip-m765-m748_M9.json",
                     "certificates/n9-stage-a5v2-strip-m765-m748_M10.json"]
            found = [c for c in cands if (REPO / c).exists()]
            if not found:
                fail("G3 certified 分支：v2 证书不在盘")
            for crel in found:
                cpath = REPO / crel
                r = subprocess.run(
                    [sys.executable, "numerics/bounds/hermite_ladder.py",
                     "--verify-cert", str(cpath)], cwd=str(REPO),
                    capture_output=True, text=True)
                if r.returncode != 0:
                    fail(f"G3 证书进程外重验 exit {r.returncode}：{r.stdout[-500:]}")
                cert = jload(cpath)
                ph_ref = (camp["phase1"] if "_M9" in crel else camp["phase2"])
                if cert["claimed_bound"] != ph_ref.get("certified"):
                    fail(f"G3 {crel} claimed_bound 与账本行不逐位相等")
                from thomson_certs.exact import is_positive_definite
                n_psd = 0
                for key, mat in cert["blocks"].items():
                    if isinstance(mat[0], list):
                        if not is_positive_definite(
                                [[Fraction(x) for x in row] for row in mat]):
                            fail(f"G3 PSD 块 {key} LDLᵀ 非正定")
                        n_psd += 1
                cb = Fraction(cert["claimed_bound"])
                if not (0 < cb <= E_STAR_DEC + E_PLUS_TOL):
                    fail("G3 certified 违反 0 < c ≤ E*+1e-6")
                okmsg(f"G3 certified 分支：{crel} --verify-cert exit 0＋逐位一致＋"
                      f"{n_psd} PSD 块 LDLᵀ＋≤E*+1e-6")
        else:
            if not p1.get("certified"):
                fail("G3 blocked 分支：attempt 精确分数缺失")
            if camp.get("X9") is None:
                fail("G3 blocked 分支：X9 缺失")
            if not camp["slope_rows"]:
                fail("G3 blocked 分支：斜率行缺失")
            okmsg(f"G3 blocked 分支：attempt={p1['certified']}＋"
                  f"X9={camp['X9']['float']:.6e}＋斜率行在档")
    else:
        fail(f"G3 相位 1 结局缺失或未知：{p1.get('outcome')}")

    # ---- G4 预算门 ----
    b_ok, b_msg = check_budget(camp)
    if not b_ok:
        fail(f"G4 预算门：{b_msg}")
    t_ok, t_msg = check_phase2_rule(camp)
    if not t_ok:
        fail(f"G4 相位触发复核：{t_msg}")
    okmsg(f"G4 预算门：{b_msg}；{t_msg}")

    # ---- G5 solver_events ----
    ev = jload(EVENTS)
    evs = ev.get("events", [])
    kinds = [e.get("event", "") for e in evs]
    if not any(k.startswith("launched") for k in kinds):
        fail("G5 solver_events 缺 launched")
    if not any("poll" in k for k in kinds) and not any(
            "rss" in json.dumps(e, ensure_ascii=False) for e in evs):
        fail("G5 solver_events 缺轮询采样")
    terminal = [k for k in kinds if k in
                ("solved_certified", "solved_blocked", "killed_timeout",
                 "guard_kill", "phase0_complete", "rss_summary", "error",
                 "phase2_not_triggered")]
    if not terminal:
        fail("G5 solver_events 缺终局事件")
    blob = json.dumps(ev, ensure_ascii=False)
    if "GUARD" not in blob and "零 GUARD" not in blob and "峰值" not in blob:
        fail("G5 solver_events 缺 GUARD/零 GUARD/峰值声明")
    okmsg(f"G5 solver_events 完整（{len(evs)} 事件：launched/poll/终局/护栏声明）")

    # ---- G6 幂等重装配 ----
    rebuilt = assemble_campaign()
    a = json.dumps(rebuilt, ensure_ascii=False, indent=1).encode()
    b_disk = CAMPAIGN.read_bytes()
    ha, hb = hashlib.sha256(a).hexdigest(), hashlib.sha256(b_disk).hexdigest()
    if ha != hb:
        fail(f"G6 幂等重装配 sha256 不一致：{ha[:16]} vs {hb[:16]}")
    okmsg(f"G6 幂等重装配 sha256 逐位一致（{ha[:16]}…）")

    # ---- G7 D31 ----
    if "### D31" not in DECISIONS.read_text():
        fail("G7 notes/decisions.md 缺 D31 裁决留痕")
    okmsg("G7 decisions D31 在档")

    # ---- 负对照 NC1：/tmp 证书篡改 ⇒ 重验失配 exit 1 ----
    cert_target = None
    for cand in ("certificates/n9-stage-a5v2-strip-m765-m748_M9.json",
                 "certificates/n9-stage-a5v2-strip-m765-m748_M10.json",
                 "certificates/n9-stage-a5-hermite-cap-m0748_M8.json"):
        if (REPO / cand).exists():
            cert_target = REPO / cand
            break
    if cert_target is None:
        fail("NC1 无可用证书作篡改演练")
    with tempfile.TemporaryDirectory() as td:
        tpath = Path(td) / cert_target.name
        cj = jload(cert_target)
        cj["claimed_bound"] = str(Fraction(cj["claimed_bound"])
                                  + Fraction(1, 10 ** 9))
        tpath.write_text(json.dumps(cj, ensure_ascii=False))
        r = subprocess.run([sys.executable, "numerics/bounds/hermite_ladder.py",
                            "--verify-cert", str(tpath)], cwd=str(REPO),
                           capture_output=True, text=True)
        if r.returncode == 0:
            fail("NC1 未检出篡改（claimed_bound+1e-9 重验仍 exit 0）")
        okmsg(f"NC1 证书篡改（claimed_bound+1e-9）⇒ 重验 exit {r.returncode} 检出 ✓")
        # 原件 sanity：未篡改时 exit 0
        r0 = subprocess.run([sys.executable, "numerics/bounds/hermite_ladder.py",
                             "--verify-cert", str(cert_target)], cwd=str(REPO),
                            capture_output=True, text=True)
        if r0.returncode != 0:
            fail(f"NC1 原件重验异常 exit {r0.returncode}")
        okmsg("NC1 原件（未篡改）重验 exit 0 ✓")

    # ---- NC2：/tmp 伪造 solve_s 超线 ⇒ G4 检出 ----
    fake = json.loads(json.dumps(camp))
    fake["budget"]["solve_s_total"] = 200000.0
    fake["phase1"]["solve_s"] = 200000.0
    b2ok, _ = check_budget(fake)
    if b2ok:
        fail("NC2 未检出伪造 solve_s 超线")
    okmsg("NC2 伪造 solve_s=200000s（18.5 当量 > 9.30）⇒ G4 检出 ✓")

    # ---- NC3：/tmp 伪造「X9<阈却启动相位 2」事件流 ⇒ G4 规则回归检出 ----
    fake3 = json.loads(json.dumps(camp))
    fake3["phase2"]["launched"] = True
    fake3["phase2"]["trigger_eval"] = dict(
        X9_ge_threshold=False, phase1_actual_le_32400=True,
        budget_headroom=True, all=False,
        solve_s_actual=str(Fraction(camp["phase1"].get("solve_s") or 30000)))
    t3ok, _ = check_phase2_rule(fake3)
    if t3ok:
        fail("NC3 未检出 X9<阈启动相位 2 的违规事件流")
    okmsg("NC3 伪造「X9<阈启动相位 2」⇒ G4 规则回归检出 ✓")

    print("[gate] 全门 PASS（G1–G7 ＋ NC1–NC3）", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser(description="R8B engine-v2-strip 验收门")
    ap.add_argument("--assemble", action="store_true",
                    help="幂等装配 results/hermite_v2_campaign.json")
    args = ap.parse_args()
    if args.assemble:
        camp = assemble_campaign()
        CAMPAIGN.write_text(json.dumps(camp, ensure_ascii=False, indent=1))
        print(f"[assemble] {CAMPAIGN}（sha256="
              f"{hashlib.sha256(CAMPAIGN.read_bytes()).hexdigest()[:16]}…）",
              flush=True)
        return
    run_gate()


if __name__ == "__main__":
    main()
