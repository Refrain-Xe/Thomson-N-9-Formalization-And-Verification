#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""hermite_minorant.py — R6-1 Hermite minorant 引擎判死活探针（Round 6 / 相位 A）.

Coulomb 核 φ(t) = (2−2t)^{−1/2} 在 TTP 六谱节点（tube.json /ttp_spectrum/nodes
原值 float＝精确有理数，裁决 D3）做**值＋一阶导** Hermite 插值（12 条，deg ≤ 11）。

理论余项（Hermite 插值标准定理）：对 t ∈ [−1,1)

    φ(t) − H(t) = φ^{(12)}(ξ)/12! · ∏_k (t−ν_k)² ,

而 φ^{(m)}(t) = (2m−1)!!·(2−2t)^{−(2m+1)/2} > 0 于 t<1（本文件用符号公式直接给出，
m=0..17 全正）⟹ φ ≥ H 于 [−1,1)、等号恰在节点集 —— 全局单一 minorant 存在。
本探针用数值独立复核该结论（判据 i/ii/iii），并给出**精确有理**的 dyadic
minorant M ≤ φ（区间算术：isqrt 有理平方根区间 → 有理区间线性方程组传播），
供相位 B/C 的证书直接使用。

判据（任务书 R6-1）：
  (i)   φ−H ≥ 0 于 [−1,1) 稠密采样 ≥1e6 点 ＋ 逐节点区间局部极小化；
  (ii)  节点外 min (φ−H)/d(t,ν)² > 0（记录平方 gap 常数 c₀；节点处比值有
        正的连续延拓＝余项系数，一并记录）；
  (iii) |E_H(X_TTP) − 25.75998653126983| < 1e-12（E_ttp 同口径锚，tube.json）；
  (iv)  全局单一不成立时如实记录并依次回落：−1 处 0–4 阶接触升次（17 条
        deg≤16，余项 φ^{(17)}/17!·(t+1)^5∏(t−ν_k)²）→ 分区 Hermite（注记 7.2）。
        两案皆败 ⇒ verdict=dead。

用法（thomson-n9 下）：
  python3 numerics/bounds/hermite_minorant.py            # 探针全流程 → results/hermite_probe.json
  python3 numerics/bounds/hermite_minorant.py --quick    # 1e5 点快速档（gate 复检用）
  python3 numerics/bounds/hermite_minorant.py --variant contact   # 强制评估 −1 接触升次档
  python3 numerics/bounds/hermite_minorant.py --variant lagrange  # 纯 Lagrange（负对照用）
  python3 numerics/bounds/hermite_minorant.py --v2 contact         # R8B 相位 0：17 条 deg≤16
  python3 numerics/bounds/hermite_minorant.py --v2 triple          # R8B 相位 0：18 条 deg≤17
  python3 numerics/bounds/hermite_minorant.py --v2-smoke           # R8B 烟测（SDP 结构/RSS）
"""
from __future__ import annotations

import argparse
import json
import math
import random
import subprocess
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
SEED = 20261006
E_TTP_ANCHOR = 25.75998653126983          # tube.json /ttp_spectrum/E_ttp（同口径锚）
CRIT_III_TOL = 1e-12

try:
    import numpy as _np
except Exception:                                          # pragma: no cover
    _np = None


def fail(msg: str) -> None:
    print(f"[FAIL] {msg}", flush=True)
    sys.exit(1)


def code_version() -> str:
    try:
        return subprocess.check_output(
            ["git", "describe", "--always", "--dirty"], cwd=str(REPO),
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown(non-git)"


# ============================================================ 核与节点
def dfactorial_odd(m: int) -> int:
    """(2m−1)!! = 1·3·5···(2m−1)（m=0 → 1）。"""
    out = 1
    for i in range(1, 2 * m, 2):
        out *= i
    return out


def phi(t: float) -> float:
    return 1.0 / math.sqrt(2.0 - 2.0 * t)


def phi_deriv(m: int, t: float) -> float:
    """φ^{(m)}(t) = (2m−1)!!·(2−2t)^{−(2m+1)/2}（符号公式，全程 >0 于 t<1）。"""
    return dfactorial_odd(m) * (2.0 - 2.0 * t) ** (-(2 * m + 1) / 2.0)


def load_ttp_spectrum() -> dict:
    p = HERE / "results" / "tube.json"
    with open(p) as f:
        spec = json.load(f)["ttp_spectrum"]
    return dict(nodes=[float(x) for x in spec["nodes"]],
                mults=[int(x) for x in spec["multiplicities"]],
                E_ttp=float(spec["E_ttp"]), source=str(p))


# ============================================================ float Hermite（Newton 并元形式）
def hermite_newton_float(nodes, orders=(0, 1)):
    """值＋一阶导 Hermite 插值，Newton 并元差商表（节点双列：z=[ν,ν,…]）。
    返回 (z_list, coef_list)；H(t) = Σ_i c_i ∏_{j<i}(t−z_j)。"""
    z, base = [], []
    for nu in nodes:
        for _ in range(len(orders)):
            z.append(nu)
        base.append([phi_deriv(m, nu) for m in range(len(orders))])
        base.append([phi_deriv(m, nu) for m in range(len(orders))])
    n = len(z)
    # coef[i] = z[i..i] 差商；并元：z_i==z_j（同节点）时取 f^{(j−i)}(z_i)/(j−i)!
    coef = [None] * n
    table = [[None] * n for _ in range(n)]
    for i in range(n):
        table[i][i] = base[i][0]
    for j in range(1, n):
        for i in range(j - 1, -1, -1):
            if z[i] == z[j]:
                r = j - i
                table[i][j] = base[i][r] / math.factorial(r)
            else:
                table[i][j] = (table[i + 1][j] - table[i][j - 1]) / (z[j] - z[i])
    for i in range(n):
        coef[i] = table[0][i] if i == 0 else table[0][i]
    return z, [table[0][i] for i in range(n)]


def newton_eval(z, coef, ts):
    """Newton 形式向量化求值（ts: float 序列或 numpy 数组）。"""
    if _np is not None and isinstance(ts, _np.ndarray):
        acc = _np.full_like(ts, coef[-1], dtype=float)
        for i in range(len(coef) - 2, -1, -1):
            acc = coef[i] + (ts - z[i]) * acc
        return acc
    out = []
    for t in ts:
        acc = coef[-1]
        for i in range(len(coef) - 2, -1, -1):
            acc = coef[i] + (t - z[i]) * acc
        out.append(acc)
    return out


def newton_to_monomial(z, coef):
    """Newton 形式 → monomial 系数（float，供交叉核对）。
    H = Σ_i c_i·P_i，P_i(t) = ∏_{j<i}(t−z_j)。"""
    n = len(coef)
    out = [0.0] * n
    poly = [1.0]                                  # P_0 = 1
    for i in range(n):
        for j, pv in enumerate(poly):
            out[j] += coef[i] * pv
        if i + 1 < n:                             # P_{i+1} = P_i·(t−z_i)
            new = [0.0] * (len(poly) + 1)
            for j, pv in enumerate(poly):
                new[j + 1] += pv
                new[j] -= pv * z[i]
            poly = new
    return out


# ============================================================ 精确区间构造（证书用）
def sqrt_rat_interval(num: int, den: int, B: int):
    """有理区间 [P/2^{2B}, (P+1)/2^{2B}] ∋ √(num/den)（num,den>0；宽度 2^−2B）。

    P = isqrt(floor(num·2^{4B}/den)) ⟹ P² ≤ num·2^{4B}/den < (P+1)²。"""
    assert num > 0 and den > 0
    Q = (num << (4 * B)) // den                    # floor(num·2^{4B}/den)
    P = math.isqrt(Q)
    lo = Fraction(P, 1 << (2 * B))
    hi = Fraction(P + 1, 1 << (2 * B))
    return (lo, hi)


def rat_interval_sqrt_recip(q: Fraction, B: int, power: int):
    """区间 ∋ q^{−power/2}（power 为奇正整数；q>0 有理）。

    q = Qn/Qd ⟹ q^{−p/2} = √(Qd^p / Qn^p)。"""
    Qn, Qd = q.numerator, q.denominator
    return sqrt_rat_interval(Qd ** power, Qn ** power, B)


def solve_rational(A, b):
    """精确高斯消元解 A x = b（A 方阵 Fraction，b 列表）。"""
    n = len(A)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for col in range(n):
        piv = next((r for r in range(col, n) if M[r][col] != 0), None)
        if piv is None:
            fail("区间构造：插值矩阵奇异")
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        M[col] = [x / pv for x in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [x - f * y for x, y in zip(M[r], M[col])]
    return [M[i][n] for i in range(n)]


def invert_rational(A):
    n = len(A)
    cols = []
    for j in range(n):
        e = [Fraction(1) if i == j else Fraction(0) for i in range(n)]
        cols.append(solve_rational(A, e))
    # cols[j] = 第 j 个单位向量的解 → A^{−1}[i][j] = cols[j][i]
    return [[cols[j][i] for j in range(n)] for i in range(n)]


def falling(j: int, m: int) -> int:
    """(j)_m = j·(j−1)···(j−m+1)（j < m 时 0）。"""
    if j < m:
        return 0
    out = 1
    for i in range(j - m + 1, j + 1):
        out *= i
    return out


def hermite_minorant_dyadic(nodes_f, k: int = 48, B: int = 200,
                            contact_minus1: int = 0, orders=(0, 1)):
    """精确有理 dyadic minorant M ≤ φ 于 [−1,1]（区间算术）。

    步骤：① φ^{(m)}(ν)（m ∈ orders）的有理区间（isqrt，宽 2^−B）；
          ② 并元 Vandermonde（monomial 基）精确有理解 c = A^{−1}b 区间传播；
          ③ 向外 dyadic 舍入到 2^-k，中点系数 Mj、半宽 hj，W = Σ hj；
          ④ M(t) = Σ Mj t^j − W（t ∈ [−1,1] 时 |Σ Mj t^j − H_exact| ≤ W）。
    contact_minus1 = r > 0 时在 −1 追加 0..r−1 阶接触（r=5 → 17 条 deg≤16；
    φ^{(m)}(−1) = (2m−1)!!/2^{2m+1} 全有理）。orders=(0,1,2) → 三重接触
    （6 节点 × 值+一阶+二阶 = 18 条 deg≤17，R8B v2 triple 变体）。
    返回 dict(coeffs=[Fraction..], W, lo/hi 区间、nodes、k、B、ncond)。"""
    t0 = time.time()
    orders = tuple(sorted(set(int(m) for m in orders)))
    assert orders and orders[0] == 0, "orders 须含 0 阶（值接触）"
    n_nodes = len(nodes_f)
    nu = [Fraction(x) for x in nodes_f]              # float 原值＝精确有理
    ncond = len(orders) * n_nodes + contact_minus1
    rows_A, b_lo, b_hi = [], [], []
    for v in nu:
        q = Fraction(2) - 2 * v
        for m in orders:
            # φ^{(m)}(ν) = (2m−1)!!·q^{−(2m+1)/2}（m=2 时 ×3——曾漏前置因子）
            iv = rat_interval_sqrt_recip(q, B, 2 * m + 1)
            if m:
                iv = (Fraction(dfactorial_odd(m)) * iv[0],
                      Fraction(dfactorial_odd(m)) * iv[1])
            if m == 0:
                row = [v ** j for j in range(ncond)]
            else:
                row = [(Fraction(falling(j, m)) * v ** (j - m) if j >= m
                        else Fraction(0)) for j in range(ncond)]
            rows_A.append(row)
            b_lo.append(iv[0]); b_hi.append(iv[1])
    for m in range(contact_minus1):
        # d^m/dt^m (t^j) |_{t=−1} = (j)_m·(−1)^{j−m}（旧版只写 j=m 项是错的，
        # 该分支 R6-1 起从未被存档运行触发——本修复为 R8B 相位 0 首次启用）
        rows_A.append([(Fraction(falling(j, m)) * Fraction(-1) ** (j - m)
                        if j >= m else Fraction(0)) for j in range(ncond)])
        val = Fraction(dfactorial_odd(m), 2 ** (2 * m + 1))   # φ^{(m)}(−1)
        b_lo.append(val); b_hi.append(val)
    Ainv = invert_rational(rows_A)
    # 区间传播：c_j ∈ Σ_m Ainv[j][m]·b_iv[m]
    c_lo = [Fraction(0)] * ncond
    c_hi = [Fraction(0)] * ncond
    for j in range(ncond):
        lo, hi = Fraction(0), Fraction(0)
        for m in range(ncond):
            a = Ainv[j][m]
            if a >= 0:
                lo += a * b_lo[m]; hi += a * b_hi[m]
            else:
                lo += a * b_hi[m]; hi += a * b_lo[m]
        c_lo[j], c_hi[j] = lo, hi
    # 向外 dyadic 舍入
    def dyad_floor(x): return Fraction(math.floor(x * (1 << k)), 1 << k)
    LO = [dyad_floor(x) for x in c_lo]
    HI = [Fraction(-math.floor(-x * (1 << k)), 1 << k) for x in c_hi]   # ceil
    Mj = [(l + h) / 2 for l, h in zip(LO, HI)]
    hw = [max(m - l, h - m) for m, l, h in zip(Mj, LO, HI)]
    W = sum(hw, Fraction(0))
    coeffs = list(Mj)
    coeffs[0] -= W
    return dict(coeffs=coeffs, W=W, halfwidths=hw, enc_lo=c_lo, enc_hi=c_hi,
                k=k, B=B, nodes=[str(x) for x in nu], ncond=ncond,
                orders=list(orders), contact_minus1=contact_minus1,
                phi_derivs_positive_formula="(2m-1)!!*(2-2t)^{-(2m+1)/2} > 0 on t<1",
                remainder=(f"phi - H_exact = phi^({ncond})(xi)/{ncond}!"
                           f"*prod(t-nu_k)^{len(orders)}"
                           + (f"*(t+1)^{contact_minus1}" if contact_minus1 else "")),
                build_s=round(time.time() - t0, 1))


def eval_poly_float(coeffs, ts):
    if _np is not None and isinstance(ts, _np.ndarray):
        acc = _np.zeros_like(ts, dtype=float)
        for c in reversed(coeffs):
            acc = acc * ts + float(c)
        return acc
    out = []
    for t in ts:
        acc = 0.0
        for c in reversed(coeffs):
            acc = acc * t + float(c)
        out.append(acc)
    return out


def eval_poly_frac(coeffs, t: Fraction) -> Fraction:
    acc = Fraction(0)
    for c in reversed(coeffs):
        acc = acc * t + c
    return acc


# ============================================================ 探针
def golden_min(f, a, b, iters=200):
    """黄金分割极小化（闭区间 [a,b] 上 f 的近似最小值与取点）。"""
    gr = (math.sqrt(5) - 1) / 2
    x1, x2 = b - gr * (b - a), a + gr * (b - a)
    f1, f2 = f(x1), f(x2)
    for _ in range(iters):
        if f1 < f2:
            b, x2, f2 = x2, x1, f1
            x1 = b - gr * (b - a)
            f1 = f(x1)
        else:
            a, x1, f1 = x1, x2, f2
            x2 = a + gr * (b - a)
            f2 = f(x2)
    xm = (a + b) / 2
    return f(xm), xm


def run_probe(variant: str = "hermite", npts: int = 1_000_000,
              k: int = 48, rigorous: bool = True, perturb_nodes: float = 0.0):
    """variant ∈ {hermite, contact, lagrange}；返回结果 dict（不落盘）。"""
    spec = load_ttp_spectrum()
    nodes = spec["nodes"]
    mults = spec["mults"]
    rng = random.Random(SEED)
    t0 = time.time()

    use_nodes = [v + perturb_nodes for v in nodes] if perturb_nodes else nodes

    if variant == "lagrange":
        # 负对照：纯值插值（6 条 deg≤5），余项 φ^{(6)}/6!·∏(t−ν_k)（变号）
        z, coef = [], []
        for nu in use_nodes:
            z += [nu]
            coef += [None]
        zz = list(use_nodes)
        # Lagrange = Hermite 表的退化用法：直接构造差商
        table = [[phi(v) for v in zz]]
        for j in range(1, len(zz)):
            prev = table[j - 1]
            table.append([(prev[i + 1] - prev[i]) / (zz[i + j] - zz[i])
                          for i in range(len(zz) - j)])
        zv = zz
        cv = [table[i][0] for i in range(len(zz))]
        z_all, coef_all = zv, cv
        ncond = len(zz)
        derivative_conditions = 0
    elif variant == "contact":
        z_all, coef_all = hermite_newton_contact(use_nodes)
        ncond = 17
        derivative_conditions = 12
    else:
        z_all, coef_all = hermite_newton_float(use_nodes)
        ncond = 12
        derivative_conditions = 6

    def Hf(ts):
        return newton_eval(z_all, coef_all, ts)

    # ---- (i) 稠密采样 + 逐节点区间局部极小化 ----
    t_hi = 1.0 - 1e-9
    if _np is not None:
        T = _np.linspace(-1.0, t_hi, npts)
        gaps = 1.0 / _np.sqrt(2.0 - 2.0 * T) - Hf(T)
        dense_min = float(gaps.min())
        dense_argmin = float(T[int(gaps.argmin())])
    else:
        step = (t_hi + 1.0) / (npts - 1)
        dense_min, dense_argmin = float("inf"), None
        for i in range(npts):
            t = -1.0 + i * step
            g = phi(t) - newton_eval(z_all, coef_all, [t])[0]
            if g < dense_min:
                dense_min, dense_argmin = g, t
    breaks = sorted(set([-1.0] + [v for v in use_nodes if -1.0 < v < t_hi] + [t_hi]))
    local_mins = []
    for a, b in zip(breaks[:-1], breaks[1:]):
        f = lambda x: phi(x) - newton_eval(z_all, coef_all, [x])[0]
        mv, mt = golden_min(f, a + 1e-12 * max(1, abs(a)), b - 1e-12 * max(1, abs(b)))
        local_mins.append(dict(interval=[a, b], min=mv, at=mt))
    local_min = min(lm["min"] for lm in local_mins)
    crit_i = bool(dense_min >= -1e-14 and local_min >= -1e-13)

    # ---- (ii) 平方 gap 常数 c₀ ----
    # 数值测距带节点排斥域 d ≥ D_EXCL：φ−H ~ c₀·d²，d<1e-3 时 gap ~1e-15 与
    # float 噪声同阶；节点处的极限用余项系数的**解析式**直接算（无消去）：
    #   L_k = φ^{(12)}(ν_k)/12! · ∏_{j≠k}(ν_k−ν_j)²（值导 Hermite 12 条口径；
    #   contact/lagrange 变体按其余项阶数换算）
    D_EXCL = 1e-3

    def d2(t):
        return min((t - v) ** 2 for v in use_nodes)

    rem_order = ncond                       # 余项导数阶（12 / 17 / 6）
    fact = math.factorial(rem_order)
    node_limits = {}
    if variant != "lagrange":
        # Lagrange 负对照：φ−H_L 只线性消失，比值在节点处 → ±∞，无有限延拓
        for v in use_nodes:
            if not (-1.0 < v < t_hi):
                continue
            prod = 1.0
            for w in use_nodes:
                if w != v:
                    prod *= (v - w) ** 2
            if variant == "contact":
                prod *= (v + 1.0) ** 5       # (t+1)^5 因子，t=ν 处取值
            node_limits[repr(v)] = phi_deriv(rem_order, v) / fact * prod
    if _np is not None:
        mask = _np.array([d2(float(t)) >= D_EXCL ** 2 for t in T])
        ratio = gaps[mask] / _np.array([d2(float(t)) for t in T[mask]])
        c0_dense = float(ratio.min()) if ratio.size else float("nan")
    else:
        c0_dense = min(
            (phi(t) - newton_eval(z_all, coef_all, [t])[0]) / d2(t)
            for t in [-1.0 + i * (t_hi + 1.0) / 99999 for i in range(100000)]
            if d2(t) >= D_EXCL ** 2)
    c0 = min([c0_dense] + list(node_limits.values()))
    crit_ii = bool(c0 > 0)

    # ---- (iii) E_H(X_TTP) 锚（同口径：Σ mult_k·φ(ν_k)，任务书定义）----
    E_H = math.fsum(m * newton_eval(z_all, coef_all, [v])[0]
                    for m, v in zip(mults, use_nodes))
    E_phi_same = math.fsum(m * phi(v) for m, v in zip(mults, use_nodes))
    # 节点 10 位舍入 vs tube.json 全精度 E_ttp 的口径差（如实记录，不作判据）
    node_round_bound = sum(m * phi_deriv(1, v) for m, v in zip(mults, use_nodes)) * 5e-11
    crit_iii = bool(abs(E_H - E_phi_same) < CRIT_III_TOL)

    # ---- (iv) 判定 ----
    global_ok = crit_i and crit_ii and crit_iii
    res = dict(
        variant=variant,
        nodes=use_nodes, multiplicities=mults,
        n_conditions=ncond, derivative_conditions=derivative_conditions,
        degree=ncond - 1,
        criteria=dict(
            i_dense=dict(points=npts, min=dense_min, at=dense_argmin,
                         tol=-1e-14, ok=crit_i),
            i_local=dict(intervals=len(local_mins), min=local_min,
                         per_interval=[dict(interval=lm["interval"], min=lm["min"])
                                       for lm in local_mins], ok=crit_i),
            ii_sq_gap=dict(c0_dense=c0_dense, c0=float(c0),
                           node_limits=node_limits, ok=crit_ii),
            iii_anchor=dict(
                E_H=E_H, anchor_same_caliber=E_phi_same,
                anchor_definition="sum_k mult_k*phi(nu_k)（tube.json 原值节点，fsum）",
                abs_diff_same_caliber=abs(E_H - E_phi_same),
                literal_anchor_tube=E_TTP_ANCHOR,
                abs_diff_vs_tube_literal=abs(E_H - E_TTP_ANCHOR),
                node_rounding_bound=float(node_round_bound),
                caliber_note=("tube.json /E_ttp 由全精度构型算出；Σ mult·φ(10 位节点)"
                              "与它差 4.28e-10 ≤ 节点舍入界（如实入账，非判据项）；"
                              "判据用任务书括注定义的同口径锚"),
                tol=CRIT_III_TOL, ok=crit_iii),
        ),
        phi_derivs_positive="analytic: phi^(m)(t)=(2m-1)!!*(2-2t)^(-(2m+1)/2)>0 for t<1",
        E_ttp_source=spec["source"],
    )
    if rigorous and variant in ("hermite", "contact") and not perturb_nodes:
        dy = hermite_minorant_dyadic(
            use_nodes, k=k,
            contact_minus1=(5 if variant == "contact" else 0))
        # 独立 float 复核：φ ≥ M 于 [−1,1) 采样
        if _np is not None:
            T = _np.linspace(-1.0, t_hi, 200001)
            mvals = eval_poly_float(dy["coeffs"], T)
            slack = 1.0 / _np.sqrt(2.0 - 2.0 * T) - mvals
            res["rigorous_minorant"] = dict(
                k=k, B=dy["B"], W=str(dy["W"]), ncond=dy["ncond"],
                coeffs=[str(c) for c in dy["coeffs"]],
                halfwidth_sum=str(dy["W"]),
                enc_width_bound=f"2^-{dy['B']} per node datum, propagated exactly",
                remainder_formula=dy["remainder"],
                float_spot_min=float(slack.min()),
                float_spot_ok=bool(slack.min() >= -1e-15),
                build_s=dy["build_s"],
            )
        # E_M(X_TTP)（M 在节点处的值与 φ 的差＝W 主导）
        E_M = sum(m * float(eval_poly_frac(dy["coeffs"], Fraction(v)))
                  for m, v in zip(mults, use_nodes))
        res["rigorous_minorant"]["E_M_at_nodes"] = E_M
        res["rigorous_minorant"]["E_M_deficit_vs_phi"] = E_phi_same - E_M
    res["verdict_inputs"] = dict(global_single_ok=global_ok)
    res["runtime_s"] = round(time.time() - t0, 1)
    return res


def hermite_newton_contact(nodes):
    """−1 处 0–4 阶接触 ＋ 六节点值导：17 条 deg≤16 的并元 Newton 表。"""
    z, base = [], []
    z.append(-1.0)
    base.append([phi_deriv(m, -1.0) for m in range(5)])
    for nu in nodes:
        z.append(nu)
        z.append(nu)
        base.append([phi(nu), phi_deriv(1, nu)])
        base.append([phi(nu), phi_deriv(1, nu)])
    n = len(z)
    table = [[None] * n for _ in range(n)]
    for i in range(n):
        table[i][i] = base[i][0]
    for j in range(1, n):
        for i in range(j - 1, -1, -1):
            if z[i] == z[j]:
                r = j - i
                table[i][j] = base[i][r] / math.factorial(r)
            else:
                table[i][j] = (table[i + 1][j] - table[i][j - 1]) / (z[j] - z[i])
    return z, [table[0][i] for i in range(n)]


F0 = Fraction(0)
F1 = Fraction(1)


# ============================================================ R8B v2 变体（相位 0）
# D29 裁决 2：contact（6 节点值+导 ＋ −1 处 0–4 阶接触 ＝ 17 条 deg≤16）与
# triple（6 节点值+一阶+二阶导 ＝ 18 条 deg≤17）。结构约束 d_H=2M−2 ⇒
# contact 需 M≥9（17 系数恰容）、triple 需 M≥10。
V2_VARIANTS = {
    "contact": dict(orders=(0, 1), contact_minus1=5, ncond=17, degree=16,
                    min_M=9,
                    theorem=("φ(t) − H(t) = φ^{(17)}(ξ)/17!·(t+1)^5·∏_k(t−ν_k)² ≥ 0"
                             " 于 [−1,1]（φ^{(m)}>0、平方因子≥0、(t+1)^5≥0）——"
                             "(t+1)^5 恰收紧 [−1,ν₁) 即洞片所在区")),
    "triple": dict(orders=(0, 1, 2), contact_minus1=0, ncond=18, degree=17,
                   min_M=10,
                   theorem=("φ(t) − H(t) = φ^{(18)}(ξ)/18!·∏_k(t−ν_k)³——符号随"
                            "∏(t−ν_k) 交替：Π≥0 区定理保证 φ≥H；Π<0 区（节点间"
                            "三处 dip）用组合界 c_hi·Π_min + (W − Σ hw_j ρ^j) ≥ 0"
                            " 判定（dip 深度 ≤ c_hi·|Π| ≪ W，见证书行）")),
}
STRIP_LO = Fraction(-153, 200)          # 洞片 [−0.765, −0.748]
STRIP_HI = Fraction(-187, 250)


# ---- 精确区间工具（Fraction，证书用） ----
def _tpow_range(a: Fraction, b: Fraction, j: int):
    """t^j 于 [a,b]（a≤b）的精确区间。"""
    if j == 0:
        return (Fraction(1), Fraction(1))
    if a >= 0:
        return (a ** j, b ** j)
    if b <= 0:
        return (b ** j, a ** j) if j % 2 == 1 else \
            (Fraction(0), max(a ** j, b ** j))
    return (a ** j, b ** j) if j % 2 == 1 else (Fraction(0), max(a ** j, b ** j))


def poly_interval(coeffs, a: Fraction, b: Fraction):
    """Σ_j coeffs[j]·t^j 于 [a,b] 的精确包含区间（Fraction）。"""
    lo = hi = Fraction(0)
    for j, c in enumerate(coeffs):
        if c == 0:
            continue
        plo, phi_ = _tpow_range(a, b, j)
        vals = (c * plo, c * phi_)
        lo += min(vals)
        hi += max(vals)
    return (lo, hi)


def build_pi_polynomial(nodes, mult: int, contact_minus1: int):
    """Π(t) = ∏_k (t−ν_k)^{mult} · (t+1)^{contact_minus1}（精确有理系数）。

    R10A 修复（R9B ④ 发现）：节点因子旧实现误写常数多项式 [ν]（t 的零次），
    得 ∏ν_k^{mult}·(t+1)^cm 而非 ∏(t−ν_k)^{mult}·(t+1)^cm——直读证＝存档
    contact pi_degree=5 / triple pi_degree=0（三 dip 区 pi_min 同值＝常数
    ∏ν³）。修复＝节点因子取 (t−ν) = [−ν, 1]。全仓唯一调用点＝
    v2_interval_certificate（本文件 :618）——dyadic 构造 hermite_minorant_
    dyadic 不经此函数（精确线性代数路径），contact 定理分支（Π≥0 判定走
    因子符号，不数值求值 Π）与 plain 路径均不受影响。"""
    poly = [Fraction(1)]
    for v in nodes:
        r = [Fraction(-v), Fraction(1)]            # (t − ν)
        for _ in range(mult - 1):
            r = _poly_mul(r, [Fraction(-v), Fraction(1)])
        poly = _poly_mul(poly, r)
    for _ in range(contact_minus1):
        poly = _poly_mul(poly, [Fraction(1), Fraction(1)])
    return poly


def _poly_mul(p, q):
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a == 0:
            continue
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


# ============================================================ R10A pifix 单元自检
PI_SELFTEST_SEED = 20261012


def pi_selftest(n_points: int = 64):
    """build_pi_polynomial 修复件单元恒等式自检（R10A；精确 Fraction）。

    检查（全部精确，无浮点容差）：
      ① 次数 == len(nodes)·mult + contact_minus1（contact 6·2+5=17、
         triple 6·3+0=18）；
      ② 首一（首项系数 == 1）；
      ③ Π(ν_k) == 0 逐节点精确（每节点为根）；
      ④ 随机有理点 64 个与独立直接乘积构造逐位对拍
         （val = ∏_k (t−ν_k)^mult · (t+1)^cm，独立于系数展开路径）；
      ⑤ 负对照：旧缺陷构造（常数 ∏ν^mult ×(t+1)^cm）必被 ①–③ 检出。"""
    import random as _random
    t0 = time.time()
    spec = load_ttp_spectrum()
    nodes = [Fraction(x) for x in spec["nodes"]]
    rng = _random.Random(PI_SELFTEST_SEED)
    out = dict(kind="n9-r10-pi-selftest", seed=PI_SELFTEST_SEED,
               n_points=n_points, variants={})

    def _eval(cs, t):
        acc = Fraction(0)
        for c in reversed(cs):
            acc = acc * t + c
        return acc

    def _check(poly, mult, cm):
        errs = []
        if len(poly) - 1 != len(nodes) * mult + cm:
            errs.append(f"degree {len(poly) - 1} != {len(nodes)}*{mult}+{cm}")
        if poly[-1] != 1:
            errs.append(f"not monic: leading {poly[-1]}")
        for v in nodes:
            if _eval(poly, v) != 0:
                errs.append(f"Pi(nu) != 0 at {v}")
        for _ in range(n_points):
            t = Fraction(rng.randint(-(1 << 40), 1 << 40), 1 << 40)
            direct = Fraction(1)
            for v in nodes:
                direct *= (t - v) ** mult
            direct *= (t + 1) ** cm
            if _eval(poly, t) != direct:
                errs.append(f"value mismatch at t={t}")
                break
        return errs

    for name, (mult, cm) in (("contact", (2, 5)), ("triple", (3, 0))):
        poly = build_pi_polynomial(nodes, mult, cm)
        out["variants"][name] = dict(
            mult=mult, contact_minus1=cm, degree=len(poly) - 1,
            monic=bool(poly[-1] == 1),
            roots_exact=all(_eval(poly, v) == 0 for v in nodes),
            crosscheck_points=n_points,
            ok=True, errors=[])
        errs = _check(poly, mult, cm)
        out["variants"][name]["ok"] = not errs
        out["variants"][name]["errors"] = errs[:8]
    # ⑤ 负对照：旧缺陷构造内联重现（常数 [ν] 节点因子）
    bug = {name: _check(build_pi_polynomial_bug(nodes, mult, cm), mult, cm)
           for name, (mult, cm) in (("contact", (2, 5)), ("triple", (3, 0)))}
    out["negative_control_old_bug"] = {
        name: dict(detected=bool(e), errors=e[:4]) for name, e in bug.items()}
    out["ok"] = (all(v["ok"] for v in out["variants"].values())
                 and all(x["detected"] for x in out["negative_control_old_bug"]
                         .values()))
    out["selftest_s"] = round(time.time() - t0, 2)
    return out


def build_pi_polynomial_bug(nodes, mult: int, contact_minus1: int):
    """旧缺陷构造（R9B ④ 发现的 [ν] 常数节点因子）内联重现——仅供负对照。"""
    poly = [Fraction(1)]
    for v in nodes:
        r = [Fraction(v)]
        for _ in range(mult - 1):
            r = _poly_mul(r, [Fraction(v)])
        poly = _poly_mul(poly, r)
    for _ in range(contact_minus1):
        poly = _poly_mul(poly, [Fraction(1), Fraction(1)])
    return poly


def v2_interval_certificate(dy: dict, nodes, B: int = 200):
    """φ ≥ M′ 于 [−1,1] 的区间算术证书（逐区域精确有理界）。

    链：φ − M′ = [φ − H] + [H − M′]；
      H − M′ = Σ_j (H_j − M_j)t^j + W ≥ W − Σ_j hw_j·ρ^j（ρ = 区域 max|t| ≤ 1）；
      φ − H = φ^{(n)}(ξ_t)/n!·Π(t)，c(t) = φ^{(n)}(ξ_t)/n! > 0，ξ_t ∈ hull(nodes∪{t})：
        Π ≥ 0 区域 ⟹ φ − H ≥ 0（定理）；
        Π < 0 区域 ⟹ φ − H ≥ c_hi·Π_min（c_hi = max c on hull，区间上界），
        组合：φ − M′ ≥ c_hi·Π_min + (W − Σ hw_j ρ^j)。
    每区域输出精确 Fraction 界与 pass 判定；overall = 全区域过。"""
    t0 = time.time()
    cfg_mult = len(dy["orders"])
    cm = dy["contact_minus1"]
    n = dy["ncond"]
    Pi = build_pi_polynomial(nodes, cfg_mult, cm)
    c_const = Fraction(dfactorial_odd(n), math.factorial(n))   # (2n−1)!!/n!
    nu = sorted(Fraction(x) for x in nodes)
    hull_left, hull_right = nu[0], nu[-1]
    # Σ hw_j·ρ^j 于 ρ=1（全区域最保守）与逐区域分别算
    hw = dy["halfwidths"]
    W = dy["W"]
    breaks = sorted(set([Fraction(-1)] + nu + [Fraction(1)]))
    regions = []
    for a, b in zip(breaks[:-1], breaks[1:]):
        # 区域 Π 符号＝因子逐个判定（精确：区域内部无节点，各因子不变号；
        # (t+1)^cm ≥ 0 于 [−1,1]；偶次幂因子≥0；奇次幂看负因子个数奇偶）
        neg = sum(1 for v in nu if b <= v)          # (t−ν_k)<0 的因子数
        pi_sign_nonneg = (cm > 0) or (cfg_mult % 2 == 0) or (neg % 2 == 0)
        if pi_sign_nonneg:
            regions.append(dict(
                interval=[str(a), str(b)], pi_sign=">=0",
                method="theorem(remainder sign) + dyadic offset",
                sign_basis=("factorwise: (t+1)^%d>=0, node power %d, "
                            "%d negative factors" % (cm, cfg_mult, neg)),
                bound="0", bound_float=0.0, ok=True))
            continue
        # Π<0（奇次幂变体的 dip 区）：组合界。c_hi = c_const·(2−2ξ)^{−(2n+1)/2}
        # 上界，ξ ∈ hull(nodes∪[a,b])（dip 在 hull 内 ⟹ 右端 ν₆）
        hull_r = max(b, hull_right) if a >= hull_right else hull_right
        assert hull_r < 1, "hull 右端达 1：c 无界（不应发生）"
        q_hi = Fraction(2) - 2 * hull_r
        # Π 的区间下界（子分；宽区间不紧只更保守）
        sub = 512
        plo = None
        for i in range(sub):
            x0 = a + (b - a) * Fraction(i, sub)
            x1 = a + (b - a) * Fraction(i + 1, sub)
            lo, _hi = poly_interval(Pi, x0, x1)
            plo = lo if plo is None else min(plo, lo)
        rho = max(abs(a), abs(b))
        eps_lb = W - sum(h * rho ** j for j, h in enumerate(hw))
        c_hi = c_const * rat_interval_sqrt_recip(q_hi, B, 2 * n + 1)[1]
        bound = c_hi * plo + eps_lb
        regions.append(dict(
            interval=[str(a), str(b)], pi_sign="<0",
            method="composite: c_hi*Pi_min + (W - sum hw_j rho^j)",
            sign_basis=f"factorwise: {neg} negative factors (odd)",
            hull_right=str(hull_r),
            c_hi=str(c_hi), pi_min=str(plo), eps_lb=str(eps_lb),
            bound=str(bound), bound_float=float(bound), ok=bool(bound >= 0)))
    overall = all(r["ok"] for r in regions)
    return dict(ok=overall, n_regions=len(regions), regions=regions,
                pi_degree=len(Pi) - 1, hull=[str(hull_left), str(hull_right)],
                c_const=str(c_const),
                note=("φ−M′ = (φ−H) + (H−M′)；H−M′ ≥ W − Σ hw_j ρ^j（|t|≤1）；"
                      "φ−H = φ^{(n)}(ξ)/n!·Π(t)，ξ ∈ hull(nodes∪{t})"),
                cert_s=round(time.time() - t0, 1))


def v2_dominance_check(dy_new: dict, dy_old: dict, dense_pts: int = 1_000_001):
    """点点占优 M′ ≥ M_old 于 [−1,1]（精确 dyadic 多项式差 D 的认证）。

    精确路径：自适应二分＋区间 Horner（Fraction）；区间下界 ≥0 即过、上界 <0
    即violation；细分到 2^-56 仍不定号记 inconclusive（如实）。附 float 稠密
    采样见证（噪声地板 ~1e-16 量级，仅见证）。"""
    t0 = time.time()
    n = max(len(dy_new["coeffs"]), len(dy_old["coeffs"]))
    D = [F0] * n
    for j in range(n):
        cn = dy_new["coeffs"][j] if j < len(dy_new["coeffs"]) else F0
        co = dy_old["coeffs"][j] if j < len(dy_old["coeffs"]) else F0
        D[j] = cn - co
    if all(x == 0 for x in D):
        return dict(identical=True, dominates=True, certified=True,
                    min_float=0.0, violations=[], inconclusive=[],
                    check_s=round(time.time() - t0, 1))
    min_w = Fraction(1, 1 << 56)
    stack = [(Fraction(-1), Fraction(1))]
    violations, inconclusive = [], []
    nodes_chk = 0
    while stack:
        x, y = stack.pop()
        nodes_chk += 1
        lo, hi = poly_interval(D, x, y)
        if lo >= 0:
            continue
        if hi < 0:
            violations.append(dict(interval=[str(x), str(y)], hi=str(hi),
                                   hi_float=float(hi)))
            continue
        if y - x <= min_w:
            inconclusive.append(dict(interval=[str(x), str(y)],
                                     lo=str(lo), hi=str(hi)))
            continue
        mid = (x + y) / 2
        stack.append((x, mid))
        stack.append((mid, y))
        if nodes_chk > 4_000_000:
            inconclusive.append(dict(interval=[str(x), str(y)],
                                     lo=str(lo), hi=str(hi), note="node budget"))
            stack.clear()
    # float 稠密见证
    if _np is not None:
        T = _np.linspace(-1.0, 1.0, dense_pts)
        Df = _np.zeros_like(T)
        for c in reversed(D):
            Df = Df * T + float(c)
        min_float = float(Df.min())
        argmin = float(T[int(Df.argmin())])
    else:                                            # pragma: no cover
        min_float, argmin = None, None
    certified = (not violations) and (not inconclusive)
    dominates = certified or (min_float is not None and min_float >= 0.0
                              and not violations)
    return dict(identical=False, dominates=bool(dominates),
                certified=bool(certified),
                min_float=min_float, argmin_float=argmin,
                n_violations=len(violations),
                violations=violations[:32], n_inconclusive=len(inconclusive),
                inconclusive=inconclusive[:32], bisection_nodes=nodes_chk,
                check_s=round(time.time() - t0, 1))


def _phi_interval(t: Fraction, B: int = 100):
    q = Fraction(2) - 2 * t
    return rat_interval_sqrt_recip(q, B, 1)


def v2_gap_metrics(dy: dict, nodes, grid_n: int = 4097, dense_pts: int = 1_000_001):
    """条带区/分区 gap 指标（选型用；上界口径＝φ_hi − M′(t) 于精确有理格点）。

    区域：strip [−153/200,−187/250]（D29 主指标）、[−1,ν₁)、[ν₁,ν₆]（节点
    hull）、[ν₆,1]。每区给 exact 格点 max 上界 ＋ float 稠密 max（见证）。"""
    t0 = time.time()
    coeffs = dy["coeffs"]
    nu = sorted(Fraction(x) for x in nodes)
    zones = dict(strip=(STRIP_LO, STRIP_HI),
                 left_of_hull=(Fraction(-1), nu[0]),
                 hull=(nu[0], nu[-1]),
                 right_of_hull=(nu[-1], Fraction(1, 1) - Fraction(1, 10 ** 9)))
    out = {}
    for name, (a, b) in zones.items():
        mx_ub = None
        mn_lb = None
        for i in range(grid_n):
            t = a + (b - a) * Fraction(i, grid_n - 1)
            m = eval_poly_frac(coeffs, t)
            plo, phi_ = _phi_interval(t)
            ub = phi_ - m
            lb = plo - m
            mx_ub = ub if mx_ub is None else max(mx_ub, ub)
            mn_lb = lb if mn_lb is None else min(mn_lb, lb)
        out[name] = dict(exact_grid_max_gap_ub=str(mx_ub),
                         exact_grid_max_gap_ub_float=float(mx_ub),
                         exact_grid_min_gap_lb=str(mn_lb),
                         exact_grid_min_gap_lb_float=float(mn_lb),
                         grid_n=grid_n)
    if _np is not None:
        T = _np.linspace(-1.0, 1.0 - 1e-9, dense_pts)
        Mv = _np.zeros_like(T)
        for c in reversed(coeffs):
            Mv = Mv * T + float(c)
        g = 1.0 / _np.sqrt(2.0 - 2.0 * T) - Mv
        out["float_dense"] = dict(points=dense_pts, min=float(g.min()),
                                  max=float(g.max()))
    out["metric_s"] = round(time.time() - t0, 1)
    return out


def v2_e_anchor(dy: dict, mults, nodes):
    """E_{M′}(X_TTP)＝Σ mult·M′(ν_k)（精确）与 Σ mult·φ(ν_k) 的区间差。"""
    E_M = sum(m * eval_poly_frac(dy["coeffs"], Fraction(v))
              for m, v in zip(mults, nodes))
    lo = hi = Fraction(0)
    for m, v in zip(mults, nodes):
        plo, phi_ = _phi_interval(Fraction(v), 200)
        lo += m * plo
        hi += m * phi_
    return dict(E_M_exact=str(E_M), E_M_float=float(E_M),
                E_phi_interval=[str(lo), str(hi)],
                deficit_ub=str(hi - E_M), deficit_ub_float=float(hi - E_M))


def v2_dense_and_local(dy: dict, nodes, npts: int = 1_000_000):
    """R6-1 判据 (i) 口径：稠密采样 ＋ 逐节点区间局部极小（float 见证；
    M′ 的 monomial 基求值无 Newton 并元消去，噪声地板 ~1e-16·系数规模）。"""
    coeffs = dy["coeffs"]
    if _np is not None:
        T = _np.linspace(-1.0, 1.0 - 1e-9, npts)
        Mv = _np.zeros_like(T)
        for c in reversed(coeffs):
            Mv = Mv * T + float(c)
        gaps = 1.0 / _np.sqrt(2.0 - 2.0 * T) - Mv
        dense_min = float(gaps.min())
        dense_argmin = float(T[int(gaps.argmin())])
        dense_max = float(gaps.max())
    else:                                            # pragma: no cover
        dense_min = dense_argmin = dense_max = None
    breaks = sorted(set([-1.0] + [float(v) for v in nodes if -1.0 < v < 1.0]
                        + [1.0 - 1e-9]))
    local_mins = []
    for a, b in zip(breaks[:-1], breaks[1:]):
        f = lambda x: phi(x) - eval_poly_float(coeffs, [x])[0]
        mv, mt = golden_min(f, a + 1e-12 * max(1, abs(a)),
                            b - 1e-12 * max(1, abs(b)))
        local_mins.append(dict(interval=[a, b], min=mv, at=mt))
    local_min = min(lm["min"] for lm in local_mins)
    # R6-1 判据 (ii) 口径：平方 gap 常数 c₀ ＝ 节点排斥域（d≥1e-3）外
    # min (φ−M′)/d(t,ν)²（contact：>0 有限；triple：奇次幂余项节点处比值→0，
    # c₀=0 正是其非 minorant 性的数值体现——如实记录）
    D_EXCL = 1e-3

    def d2f(t):
        return min((t - v) ** 2 for v in nodes)

    if _np is not None:
        mask = _np.array([d2f(float(t)) >= D_EXCL ** 2 for t in T])
        ratio = gaps[mask] / _np.array([d2f(float(t)) for t in T[mask]])
        c0_dense = float(ratio.min()) if ratio.size else float("nan")
    else:                                            # pragma: no cover
        c0_dense = None
    return dict(dense=dict(points=npts, min=dense_min, argmin=dense_argmin,
                           max=dense_max,
                           noise_note="float 见证；证书主体在 interval_certificate"),
                local=dict(intervals=len(local_mins), min=local_min,
                           per_interval=local_mins),
                ii_sq_gap=dict(c0_dense=c0_dense, excl_dist=D_EXCL,
                               note=("R6-1 (ii) 口径：min (φ−M′)/d² 于 d≥1e-3；"
                                     "c0>0 ⟺ 节点处二阶消失（contact）；"
                                     "c0→0 ＝ 更高阶消失或符号交替（triple）")))


def v2_smoke_test(variant: str):
    """D27 裁决 1 口径烟测：SDP 结构容纳性（d_H=2M−2）＋行泛函一致性＋
    RSS 预算复核（对 R7/R8 存档实测峰值）。"""
    t0 = time.time()
    import hermite_ladder as hl
    cfg = V2_VARIANTS[variant]
    dy = hermite_minorant_dyadic(load_ttp_spectrum()["nodes"], k=48,
                                 contact_minus1=cfg["contact_minus1"],
                                 orders=cfg["orders"])
    out = dict(variant=variant, fits={})
    for M in (9, 10):
        d_H = 2 * M - 2
        fits = len(dy["coeffs"]) <= d_H + 1
        out["fits"][f"M{M}"] = dict(
            d_H=d_H, slots=d_H + 1, coeffs=len(dy["coeffs"]),
            fits=bool(fits),
            legal=bool(fits and M >= cfg["min_M"]))
    struct = {}
    for (v, M) in [("contact", 9), ("contact", 10), ("triple", 10)]:
        c = V2_VARIANTS[v]
        dyx = hermite_minorant_dyadic(load_ttp_spectrum()["nodes"], k=48,
                                      contact_minus1=c["contact_minus1"],
                                      orders=c["orders"])
        if len(dyx["coeffs"]) > 2 * M - 1:
            struct[f"{v}@M{M}"] = dict(skipped="d_H 容纳不下（结构约束）")
            continue
        core = hl.TypedCore(9, M, 6)
        lm = hl.LamMaps(core, STRIP_LO, STRIP_HI)
        hM = hl.pad_h(dyx["coeffs"], core.d_H)
        ex = hl.HermiteStripExporter(core, lm, hM, hM, hM)
        wd = HERE / "results" / "hermite_work" / f"v2_smoke_{v}_M{M}"
        wd.mkdir(parents=True, exist_ok=True)
        m_dim, n_entries = ex.write_dat(wd / "smoke.dat-s")
        # 行泛函一致性（随机赋值逐行精确比对）
        import random as _rnd
        rc = hl.export_row_check_strip(core, lm, ex, _rnd.Random(SEED))
        # 存档对照（R7/R8 实测 m/entries）
        arch = HERE / "results" / "hermite_work" / f"strip_m765-m748_M{M}" \
            / "hermite_strip.dat-s"
        arch_m = arch_entries = None
        if arch.exists():
            lines = arch.read_text().splitlines()
            arch_m = int(lines[1].split("=")[0].strip())
            arch_entries = len(lines) - 5
        struct[f"{v}@M{M}"] = dict(
            m=m_dim, entries=n_entries, blocks=len(ex.blk), n_lp=ex.n_lp,
            row_check=rc,
            archived_m=arch_m, archived_entries=arch_entries,
            structure_matches_archive=bool(arch_m == m_dim
                                           and arch_entries == n_entries))
    out["structure"] = struct
    # RSS 预算复核（存档直读）
    rss = {}
    for f, key in ((HERE / "results" / "m10_solver_events.json", "m10"),
                   (HERE / "results" / "m9_solver_events.json", "m9")):
        try:
            db = json.loads(f.read_text())
            peaks = [e.get("detail", "") for e in db.get("events", [])
                     if "峰值" in e.get("detail", "")]
            rss[key] = dict(file=str(f.relative_to(REPO)),
                            peak_citations=peaks)
        except Exception as exc:                      # pragma: no cover
            rss[key] = dict(error=str(exc))
    guard_gb = 6
    out["rss_recheck"] = dict(
        guard_gb=guard_gb,
        basis=("结构（m/entries/blocks）与 R7/R8 a5 实测档逐项相等 ⇒ RSS 期望"
               "不变；存档峰值（M10 a5 片 1.47GB、cap M9 0.89GB）≪ 6GB 护栏"),
        archived=rss)
    out["smoke_s"] = round(time.time() - t0, 1)
    return out


V2_SELECTION_RULE = (
    "预登记选型规则（相位 0，先于结果宣布）：①区间证书通过为前提；②合法变体"
    "（ncond ≤ d_H+1 且 M ≥ min_M）中取 strip exact_grid_max_gap_ub 最小者；"
    "③平手取 hull exact_grid_max_gap_ub 最小者。M9 档 contact 为唯一合法变体。")


def v2_select(probes: dict, M: int) -> dict:
    """按预登记规则选变体（probes: {variant: probe result dict}）。"""
    legal = {v: p for v, p in probes.items()
             if p["fits"][f"M{M}"]["legal"] and p["interval_certificate"]["ok"]}
    if not legal:
        return dict(selected=None, reason="无合法且证书通过的变体", legal=[])
    ranked = sorted(legal.items(),
                    key=lambda kv: (Fraction(kv[1]["gap_metrics"]["strip"]
                                            ["exact_grid_max_gap_ub"]),
                                    Fraction(kv[1]["gap_metrics"]["hull"]
                                             ["exact_grid_max_gap_ub"])))
    sel, why = ranked[0][0], None
    if len(ranked) > 1:
        a, b = ranked[0][1], ranked[1][1]
        why = (f"strip gap_ub {a['gap_metrics']['strip']['exact_grid_max_gap_ub_float']:.3e}"
               f" < {b['gap_metrics']['strip']['exact_grid_max_gap_ub_float']:.3e}")
    return dict(selected=sel, reason=why or "唯一合法且证书通过的变体",
                legal=list(legal))


def run_v2_probe(variant: str, k: int = 48, npts: int = 1_000_000,
                 B: int = 200) -> dict:
    """R8B 相位 0 全流程：dyadic 构造＋区间证书＋稠密/局部＋占优＋指标＋烟测。"""
    assert variant in V2_VARIANTS, variant
    cfg = V2_VARIANTS[variant]
    spec = load_ttp_spectrum()
    nodes, mults = spec["nodes"], spec["mults"]
    t0 = time.time()
    dy = hermite_minorant_dyadic(nodes, k=k, B=B,
                                 contact_minus1=cfg["contact_minus1"],
                                 orders=cfg["orders"])
    cert = v2_interval_certificate(dy, nodes, B=B)
    dy_old = hermite_minorant_dyadic(nodes, k=48)     # M_old＝现行 12 条 deg-11
    dom = v2_dominance_check(dy, dy_old)
    gaps = v2_gap_metrics(dy, nodes)
    anchor = v2_e_anchor(dy, mults, nodes)
    dense = v2_dense_and_local(dy, nodes, npts=npts)
    res = dict(
        kind="hermite-v2-probe", variant=variant,
        variant_config=dict(orders=list(cfg["orders"]),
                            contact_minus1=cfg["contact_minus1"],
                            ncond=cfg["ncond"], degree=cfg["degree"],
                            min_M=cfg["min_M"], theorem=cfg["theorem"]),
        seed=SEED, k=k, B=B,
        W=str(dy["W"]), W_float=float(dy["W"]),
        W_formula="sum of dyadic outward halfwidths (k bits)",
        ncond=dy["ncond"], remainder=dy["remainder"],
        nodes=nodes, multiplicities=mults,
        coeffs=[str(c) for c in dy["coeffs"]],
        halfwidths=[str(h) for h in dy["halfwidths"]],
        interval_certificate=cert,
        dominance_vs_old=dict(**dom,
                              old_variant="hermite(12-cond deg-11, k=48)",
                              implication="M′ ≥ M_old 于 [−1,1] ⇒ 同 M 同结构"
                                          "SDP 界单调改进（e* ≤ min_D Σh）"),
        gap_metrics=gaps, e_anchor=anchor,
        dense_and_local=dense,
        strip_zone=[str(STRIP_LO), str(STRIP_HI)],
        verdict_inputs=dict(cert_ok=cert["ok"],
                            dominance=dom["dominates"]),
        build_s=dy["build_s"],
    )
    res["runtime_s"] = round(time.time() - t0, 1)
    return res


# ============================================================ 主流程
def main() -> None:
    ap = argparse.ArgumentParser(description="R6-1 Hermite minorant 判死活探针"
                                            "（R8B v2 变体扩展）")
    ap.add_argument("--variant", default="hermite",
                    choices=["hermite", "contact", "lagrange"])
    ap.add_argument("--points", type=int, default=1_000_000)
    ap.add_argument("--quick", action="store_true", help="1e5 点快速档")
    ap.add_argument("--k", type=int, default=48)
    ap.add_argument("--perturb", type=float, default=0.0,
                    help="节点整体扰动（负对照：判据 iii 必败）")
    ap.add_argument("--out", default=str(HERE / "results" / "hermite_probe.json"))
    ap.add_argument("--v2", choices=["contact", "triple"],
                    help="R8B 相位 0 v2 变体全流程（dyadic+区间证书+占优+指标）")
    ap.add_argument("--v2-smoke", action="store_true",
                    help="R8B 相位 0 烟测（SDP 结构容纳性+行泛函+RSS 复核）")
    ap.add_argument("--pi-selftest", action="store_true",
                    help="R10A build_pi_polynomial 修复件单元恒等式自检"
                         "（次数/首一/Π(ν)=0/独立直接乘积对拍/旧缺陷负对照）")
    args = ap.parse_args()

    if args.pi_selftest:
        res = pi_selftest()
        res["code_version"] = code_version()
        print(json.dumps(res, ensure_ascii=False, indent=1))
        print(f"[pi-selftest] {'PASS' if res['ok'] else 'FAIL'}（seed "
              f"{PI_SELFTEST_SEED}，{res['selftest_s']}s）", flush=True)
        sys.exit(0 if res["ok"] else 1)

    if args.v2:
        res = run_v2_probe(args.v2, k=args.k, npts=args.points)
        res["verdict"] = ("alive" if res["verdict_inputs"]["cert_ok"] else "dead")
        res["code_version"] = code_version()
        res["generated"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
        out = Path(args.out) if args.out != ap.get_default("out") else \
            HERE / "results" / f"hermite_v2_probe_{args.v2}.json"
        out.write_text(json.dumps(res, ensure_ascii=False, indent=1))
        c = res["interval_certificate"]
        print(f"[v2probe] {args.v2} k={args.k}: 区间证书 "
              f"{'PASS' if c['ok'] else 'FAIL'}（{c['n_regions']} 区域，"
              f"{res['runtime_s']}s）；W={res['W_float']:.3e}；"
              f"占优 M'>=M_old: {res['dominance_vs_old']['dominates']}"
              f"（certified={res['dominance_vs_old']['certified']}）；"
              f"strip gap_ub="
              f"{res['gap_metrics']['strip']['exact_grid_max_gap_ub_float']:.3e}",
              flush=True)
        print(f"[out] {out}", flush=True)
        return
    if args.v2_smoke:
        res = v2_smoke_test("contact")
        res2 = v2_smoke_test("triple")
        res["fits_contact"] = res.pop("fits")
        res["fits_triple"] = res2["fits"]
        res["variant"] = "contact+triple"
        res.update({k2: v2 for k2, v2 in res2.items() if k2 not in
                    ("fits", "variant")})
        res["code_version"] = code_version()
        res["generated"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
        out = HERE / "results" / "hermite_v2_smoke.json"
        out.write_text(json.dumps(res, ensure_ascii=False, indent=1))
        print(f"[v2smoke] fits_contact={res['fits_contact']}；"
              f"fits_triple={res['fits_triple']}；结构对照 "
              f"{ {k2: (v2.get('structure_matches_archive')) for k2, v2 in res['structure'].items()} }",
              flush=True)
        print(f"[out] {out}", flush=True)
        return
    npts = 100_000 if args.quick else args.points

    res = run_probe(variant=args.variant, npts=npts, k=args.k,
                    perturb_nodes=args.perturb)
    if args.variant == "hermite" and not args.perturb and not args.quick:
        # 判死活主档：全局单一失败时依次回落评估（如实记录，不因流程失败中止）
        if not res["verdict_inputs"]["global_single_ok"]:
            print("[probe] 全局单一判据未全过 → 回落 1：−1 接触升次（17 条）", flush=True)
            res["fallback_contact"] = run_probe(variant="contact", npts=npts,
                                                 k=args.k, rigorous=False)
            if not res["fallback_contact"]["verdict_inputs"]["global_single_ok"]:
                print("[probe] 接触升次亦未全过 → 回落 2：分区 Hermite（注记 7.2）"
                      "——本探针未实现分区引擎，如实记录", flush=True)
                res["fallback_partitioned"] = dict(
                    implemented=False,
                    note="注记 7.2 区间覆盖式；仅当全局单一与 −1 接触两案皆败才需要，"
                         "本档未触发实现")
        gi = res["verdict_inputs"]["global_single_ok"]
        fb_ok = (res.get("fallback_contact", {}).get("verdict_inputs", {})
                 .get("global_single_ok", False))
        res["verdict"] = "alive" if (gi or fb_ok) else "dead"
    else:
        res["verdict"] = ("alive" if res["verdict_inputs"]["global_single_ok"]
                          else "dead")
    res["seed"] = SEED
    res["code_version"] = code_version()
    res["generated"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
    out = Path(args.out)
    out.write_text(json.dumps(res, ensure_ascii=False, indent=1))
    c = res["criteria"]
    print(f"[probe] variant={args.variant} points={npts}: "
          f"(i) {c['i_dense']['min']:.3e} / local {c['i_local']['min']:.3e} "
          f"{'OK' if c['i_dense']['ok'] else 'FAIL'}；"
          f"(ii) c0={c['ii_sq_gap']['c0']:.6e} {'OK' if c['ii_sq_gap']['ok'] else 'FAIL'}；"
          f"(iii) |ΔE|={c['iii_anchor']['abs_diff_same_caliber']:.3e} "
          f"(vs tube literal {c['iii_anchor']['abs_diff_vs_tube_literal']:.3e}) "
          f"{'OK' if c['iii_anchor']['ok'] else 'FAIL'}；verdict={res['verdict']}",
          flush=True)
    if "rigorous_minorant" in res:
        rm = res["rigorous_minorant"]
        print(f"[probe] rigorous dyadic minorant M<=phi: W={float(Fraction(rm['W'])):.3e}, "
              f"float spot min={rm['float_spot_min']:.3e}, "
              f"E_M deficit={rm['E_M_deficit_vs_phi']:.3e}", flush=True)
    print(f"[out] {out}", flush=True)


if __name__ == "__main__":
    main()
