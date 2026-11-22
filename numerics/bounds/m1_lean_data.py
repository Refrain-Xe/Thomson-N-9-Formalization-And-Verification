#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""m1_lean_data.py — R12a M1 Lean 全链数据件（seed 20261014）.

任务书口径（r12a-m1-lean-e2e 相位 1）：只读消费冻结件 results/lp_m1_light.json，
产出 M1 Lean 证明所需的全部精确 Fraction 数据并落盘 results/m1_lean_data.json；
`--emit-lean` 同时从同一数据生成 formal/lean/ThomsonN9/M1Data.lean（ℚ 常量模块）。

产出内容：
  (a) f 的单项式展开（Legendre→monomial 独立 Bonnet 重推导）＋ k≥1 支集审计 {1,2,3,7}；
  (b) p(t)=1−f(t)²(2−2t) 的精确非负证书——【设计变更，见 notes/m1-lean-data.md】任务书
      预设的 ℚ 因子分解（平方/正定二次/(1±t)/正常数/不可约二次平方）经探针实证不可行：
      p 在 ℚ 上不可约（次数 15 为奇 ⇒ 有区间外实根 t₀≈−1.4233，任何"非负类因子之积"
      在 t₀ 处均不取 0，矛盾）。改用半直线 Lukács SOS 形式：
        P(u) := (1+u)^15 · p((1−u)/(1+u)) = Σᵢ d0ᵢ·z0ᵢ(u)² + u·Σᵢ d1ᵢ·z1ᵢ(u)²
      其中 z0ᵢ/z1ᵢ 为 ℚ 系数多项式（LDLᵀ 列），d0ᵢ,d1ᵢ ∈ ℚ≥0（LDLᵀ 主元，全部 > 0
      精确验证）。u ≥ 0 时右端逐项非负 ⇒ P ≥ 0 ⇒ p ≥ 0（Lean 侧 sum_nonneg＋mul_nonneg
      ＋sq_nonneg，与任务书引理族同型）。数值初值由 SDP（venv cvxpy/CLARABEL）给出，
      经零空间重参数化 + 二进有理舍入后**恒等式精确成立**（仿射结构保证）且 psd 经
      精确 Fraction LDLᵀ 验证——门 G7 以 stdlib-only 独立复核全部精确性。
  (c) 逐 k∈{1,2,3,7}：H_k=kerΔ 整数基（精确高斯消元零空间，dim=2k+1）、
      Gram R=∫hh/(4π)（公式 ∫x^{2p}y^{2q}z^{2r}dσ/4π=2(2p)!(2q)!(2r)!(n+1)!/(p!q!r!(2n+2)!）、
      精确 R⁻¹、精确 LDLᵀ（L 单位下三角＋D 对角正）、球面理想证书 A_k,B_k
      （D_k:=(2k+1)P_k(x·y)−Σ(R⁻¹)h_lh_j = (‖x‖²−1)A_k+(‖y‖²−1)B_k，字典序 Grobner
      归约链构造，范式恰为 0）。
  (d) 装配常数：ĉ_k（=lp_m1_light 冻结 c_k 逐位）、f(1)=Σĉ_k、B=(81ĉ₀−9f(1))/2 精确
      重算 == lp_m1_light.bound_exact 逐位、189/8 < B ≤ E*+1e-6（E* 只读
      thomson-workflow/data/energies.json 的 energies/9/value=25.759986531，十进制口径
      Fraction 解析）。
  provenance：seed=20261014（无随机路径，惯例记档）、code_version=git describe、
  lp_m1_light.json 的 sha256。

用法（SDP 步需仓库 venv 的 cvxpy；纯精确复核无需）：
  numerics/.venv/bin/python3 numerics/bounds/m1_lean_data.py            # 全部：json + M1Data.lean
  numerics/.venv/bin/python3 numerics/bounds/m1_lean_data.py --no-lean  # 仅 json
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
import subprocess
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                    # thomson-n9/
CAMPAIGN_ROOT = REPO.parent               # 八电子在球面的分布/
LP_LIGHT = RESULTS / "lp_m1_light.json"
ENERGIES = CAMPAIGN_ROOT / "thomson-workflow" / "data" / "energies.json"
LEAN_OUT = REPO / "formal" / "lean" / "ThomsonN9" / "M1Data.lean"
JSON_OUT = RESULTS / "m1_lean_data.json"

SEED = 20261014
KS = [1, 2, 3, 7]

# ---------------------------------------------------------------- 多项式工具
def upoly_mul(a: list[Fr], b: list[Fr]) -> list[Fr]:
    r = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r

def upoly_trunc(a: list[Fr]) -> list[Fr]:
    while a and a[-1] == 0:
        a.pop()
    return a

def lcm_den(poly) -> int:
    d = 1
    for x in poly:
        d = d * x.denominator // math.gcd(d, x.denominator)
    return d

# 3 变多项式：dict{(a,b,c): Fr}
def tri_mul(A, B):
    R = {}
    for k1, v1 in A.items():
        for k2, v2 in B.items():
            k = (k1[0] + k2[0], k1[1] + k2[1], k1[2] + k2[2])
            R[k] = R.get(k, Fr(0)) + v1 * v2
    return {k: v for k, v in R.items() if v != 0}

def tri_laplacian(A):
    R = {}
    for (a, b, c), v in A.items():
        if a >= 2:
            R[(a - 2, b, c)] = R.get((a - 2, b, c), Fr(0)) + v * a * (a - 1)
        if b >= 2:
            R[(a, b - 2, c)] = R.get((a, b - 2, c), Fr(0)) + v * b * (b - 1)
        if c >= 2:
            R[(a, b, c - 2)] = R.get((a, b, c - 2), Fr(0)) + v * c * (c - 1)
    return {k: v for k, v in R.items() if v != 0}

def tri_monomials(k: int):
    return [(i, j, k - i - j) for i in range(k + 1) for j in range(k + 1 - i)]

# 6 变多项式：dict{(a,b,c,d,e,g): Fr}
def hex_add(A, B):
    R = dict(A)
    for k, v in B.items():
        R[k] = R.get(k, Fr(0)) + v
    return {k: v for k, v in R.items() if v != 0}

def hex_mul(A, B):
    R = {}
    for k1, v1 in A.items():
        for k2, v2 in B.items():
            k = tuple(k1[i] + k2[i] for i in range(6))
            R[k] = R.get(k, Fr(0)) + v1 * v2
    return {k: v for k, v in R.items() if v != 0}

def hex_scale(A, c):
    return {k: v * c for k, v in A.items() if v * c != 0}

def lift_x(Hx):
    return {(a, b, c, 0, 0, 0): v for (a, b, c), v in Hx.items()}

def lift_y(Hy):
    return {(0, 0, 0, a, b, c): v for (a, b, c), v in Hy.items()}

# ---------------------------------------------------------------- 精确线代
def nullspace_frac(rows, ncols):
    m = [r[:] for r in rows]
    nrows = len(m)
    pivots = []
    r = 0
    for c in range(ncols):
        pr = next((rr for rr in range(r, nrows) if m[rr][c] != 0), None)
        if pr is None:
            continue
        m[r], m[pr] = m[pr], m[r]
        pv = m[r][c]
        m[r] = [x / pv for x in m[r]]
        for rr in range(nrows):
            if rr != r and m[rr][c] != 0:
                f = m[rr][c]
                m[rr] = [a - f * b for a, b in zip(m[rr], m[r])]
        pivots.append((r, c))
        r += 1
        if r == nrows:
            break
    freecols = [c for c in range(ncols) if c not in [p[1] for p in pivots]]
    basis = []
    for fc in freecols:
        v = [Fr(0)] * ncols
        v[fc] = Fr(1)
        for (rr, cc) in pivots:
            v[cc] = -m[rr][fc]
        basis.append(v)
    return basis

def solve_frac(rows, rhs, ncols):
    m = [r[:] + [v] for r, v in zip(rows, rhs)]
    n = len(m)
    for c in range(ncols):
        pr = next((rr for rr in range(c, n) if m[rr][c] != 0), None)
        if pr is None:
            return None
        m[c], m[pr] = m[pr], m[c]
        pv = m[c][c]
        m[c] = [x / pv for x in m[c]]
        for rr in range(n):
            if rr != c and m[rr][c] != 0:
                f = m[rr][c]
                m[rr] = [a - f * b for a, b in zip(m[rr], m[c])]
    return [m[i][ncols] for i in range(ncols)]

def mat_inv_frac(M):
    n = len(M)
    cols = []
    for j in range(n):
        e = [Fr(1) if i == j else Fr(0) for i in range(n)]
        cols.append(solve_frac(M, e, n))
    return [[cols[j][i] for j in range(n)] for i in range(n)]

def mat_mul_frac(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)] for i in range(n)]

def ldl_frac(G):
    """精确 LDLᵀ；返回 (L, D) 或 (None, None)（D 出现负主元）。"""
    n = len(G)
    L = [[Fr(1) if i == j else Fr(0) for j in range(n)] for i in range(n)]
    D = []
    W = [row[:] for row in G]
    for j in range(n):
        d = W[j][j]
        if d <= 0:
            return None, None
        D.append(d)
        for i in range(j + 1, n):
            L[i][j] = W[i][j] / d
            for jj in range(j, n):
                W[i][jj] -= L[i][j] * W[j][jj]
    return L, D

# ---------------------------------------------------------------- 球面矩
def sphere_moment(a, b, c):
    if a % 2 or b % 2 or c % 2:
        return Fr(0)
    p_, q_, r_ = a // 2, b // 2, c // 2
    n = p_ + q_ + r_
    return Fr(2 * math.factorial(a) * math.factorial(b) * math.factorial(c) * math.factorial(n + 1),
              math.factorial(p_) * math.factorial(q_) * math.factorial(r_) * math.factorial(2 * n + 2))

def gram_frac(H):
    n = len(H)
    return [[sum(v1 * v2 * sphere_moment(k1[0] + k2[0], k1[1] + k2[1], k1[2] + k2[2])
                for k1, v1 in H[i].items() for k2, v2 in H[j].items()) for j in range(n)]
            for i in range(n)]

# ---------------------------------------------------------------- Legendre（Bonnet 独立重推导）
def legendre_mono(k: int) -> list[Fr]:
    L = [[Fr(1)], [Fr(0), Fr(1)]]
    for n in range(1, k):
        nxt = [Fr(0)] * (n + 2)
        for j, a in enumerate(L[n]):
            nxt[j + 1] += Fr(2 * n + 1, n + 1) * a
        for j, a in enumerate(L[n - 1]):
            nxt[j] -= Fr(n, n + 1) * a
        L.append(nxt)
    return L[k]

# ---------------------------------------------------------------- Frobenius/Lex 归约
def reduce_ideal(D6):
    """D6 ∈ ℚ[a,b,c,d,e,g] 模 (a²+b²+c²−1, d²+e²+g²−1) 的字典序 Grobner 归约；
    归约链构造 A（前理想商）与 B（后理想商）。范式必须为 0。"""
    A, B = {}, {}
    poly = dict(D6)
    guard = 0
    while poly:
        guard += 1
        assert guard < 10_000_000, "reduction loop"
        lm = max(poly.keys())
        lc = poly[lm]
        if lm[0] >= 2:
            red = (lm[0] - 2, lm[1], lm[2], lm[3], lm[4], lm[5])
            A = hex_add(A, {red: lc})
            poly = hex_add(poly, {lm: -lc})
            poly = hex_add(poly, {red: lc})
            poly = hex_add(poly, {(red[0], red[1] + 2, *red[2:]): -lc})
            poly = hex_add(poly, {(red[0], red[1], red[2] + 2, *red[3:]): -lc})
        elif lm[3] >= 2:
            red = (lm[0], lm[1], lm[2], lm[3] - 2, lm[4], lm[5])
            B = hex_add(B, {red: lc})
            poly = hex_add(poly, {lm: -lc})
            poly = hex_add(poly, {red: lc})
            poly = hex_add(poly, {(red[0], red[1], red[2], red[3], red[4] + 2, red[5]): -lc})
            poly = hex_add(poly, {(red[0], red[1], red[2], red[3], red[4], red[5] + 2): -lc})
        else:
            raise AssertionError(f"nonzero normal form at {lm}")
    return A, B

# ================================================================ 主流程
def main() -> None:
    ap = argparse.ArgumentParser(description="R12a M1 Lean 数据件生成")
    ap.add_argument("--no-lean", action="store_true", help="不生成 M1Data.lean")
    args = ap.parse_args()
    sys.set_int_max_str_digits(2_000_000)

    random.seed(SEED)                      # 惯例记档；本脚本无随机路径
    t0 = time.time()
    lp = json.loads(LP_LIGHT.read_text())
    lp_sha = hashlib.sha256(LP_LIGHT.read_bytes()).hexdigest()

    # ---------- (a) f 单项式展开＋支集审计 ----------
    cs = [Fr(s) for s in lp["certificate"]["coeffs_legendre_exact"]]
    assert len(cs) == 9 and lp["certificate"]["degree"] == 8
    support = [k for k in range(1, 9) if cs[k] != 0]
    assert support == [1, 2, 3, 7], f"k≥1 支集失配：{support}"
    assert all(cs[k] >= 0 for k in support)
    f_mono = [Fr(0)] * 9
    for k in range(9):
        for j, a in enumerate(legendre_mono(k)):
            f_mono[j] += cs[k] * a
    upoly_trunc(f_mono)
    # P_k(1)=1 逐项审计
    for k in range(9):
        assert sum(legendre_mono(k)) == 1, f"P_{k}(1)≠1"

    # ---------- p 与 Möbius 变换 P ----------
    f2 = upoly_mul(f_mono, f_mono)
    p_poly = [Fr(1)] + [Fr(0)] * 15
    for i, x in enumerate(upoly_mul([Fr(2), Fr(-2)], f2)):
        p_poly[i] -= x
    upoly_trunc(p_poly)
    assert len(p_poly) == 16
    p_m1 = sum(((-1) ** i) * p_poly[i] for i in range(16))     # p(−1)
    assert p_m1 > 0, "p(−1) ≤ 0"
    N = 15
    P_u = [Fr(0)] * (N + 1)
    for i, pi in enumerate(p_poly):
        if pi == 0:
            continue
        row = [Fr(1)]
        for _ in range(i):
            row = upoly_mul(row, [Fr(1), Fr(-1)])
        for _ in range(N - i):
            row = upoly_mul(row, [Fr(1), Fr(1)])
        for j, x in enumerate(row):
            P_u[j] += pi * x
    upoly_trunc(P_u)
    assert len(P_u) == 16 and P_u[0] == 1

    # ---------- (b') P 的半直线 SOS 证书（SDP 初值＋精确修复） ----------
    cert = build_sos_certificate(P_u)

    # ---------- (c) 核机制 ----------
    kernels = {}
    for k in KS:
        kernels[str(k)] = build_kernel(k)

    # ---------- (d) 装配 ----------
    f1 = sum(cs)                                   # f(1) = Σĉ_k（P_k(1)=1）
    assert sum(f_mono) == f1                       # 单项式口径复核
    B = (Fr(81) * cs[0] - 9 * f1) / 2
    bound_exact = Fr(lp["bound_exact"])
    assert B == bound_exact, "B 逐位重算失配"
    energies = json.loads(ENERGIES.read_text())
    E_star = Fr(str(energies["energies"]["9"]["value"]))     # Fraction("25.759986531")
    assert Fr("25.759986531") == E_star
    assert Fr(189, 8) < B <= E_star + Fr(1, 10**6), "189/8 < B ≤ E*+1e-6 失败"

    # ---------- provenance ----------
    try:
        code_version = subprocess.run(["git", "describe", "--tags", "--always", "--dirty"],
                                      cwd=REPO, capture_output=True, text=True,
                                      timeout=30).stdout.strip()
    except Exception:
        code_version = "unknown"

    data = {
        "kind": "m1_lean_data",
        "script": "m1_lean_data.py",
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "seed": SEED,
        "source_artifact": {
            "path": "results/lp_m1_light.json",
            "sha256": lp_sha,
            "bound_exact": lp["bound_exact"],
        },
        "target": {"N": 9, "E_star": str(E_star),
                   "E_star_source": "../thomson-workflow/data/energies.json"},
        "f": {
            "coeffs_legendre_exact": [str(c) for c in cs],
            "support_k_ge_1": support,
            "monomial_coeffs": [str(x) for x in f_mono],
            "f_of_1": str(f1),
            "p_coeffs": [str(x) for x in p_poly],
            "p_of_minus_1": str(p_m1),
        },
        "pos_certificate": {
            "form": "half-line Lukacs SOS (design change; see notes/m1-lean-data.md)",
            "task_prescribed_form": "Q-factorization into nonneg classes — infeasible: p is "
                                    "Q-irreducible of odd degree 15 (real root t0≈-1.4233 outside "
                                    "[-1,1]); no product/sum of the prescribed factor classes can "
                                    "vanish at t0, hence cannot equal p",
            "moebius_P_coeffs": [str(x) for x in P_u],
            "L0": [[str(x) for x in row] for row in cert["L0"]],
            "D0": [str(x) for x in cert["D0"]],
            "L1": [[str(x) for x in row] for row in cert["L1"]],
            "D1": [str(x) for x in cert["D1"]],
            "check": cert["check"],
        },
        "kernels": kernels,
        "assembly": {
            "c0": str(cs[0]), "c1": str(cs[1]), "c2": str(cs[2]),
            "c3": str(cs[3]), "c7": str(cs[7]),
            "f_of_1": str(f1), "B": str(B),
            "bound_exact_bitwise_equal": True,
            "E_star": str(E_star), "E_star_plus_1em6": str(E_star + Fr(1, 10**6)),
            "ineq_189_8_lt_B": True, "B_le_Estar_plus_1em6": True,
        },
        "provenance": {"seed": SEED, "code_version": code_version,
                       "lp_m1_light_sha256": lp_sha,
                       "sdp": "cvxpy/CLARABEL (venv) initial point only; identity exact by "
                              "affine reparameterization, psd by exact Fraction LDL^T"},
        "runtime_s": round(time.time() - t0, 2),
        "repro": "numerics/.venv/bin/python3 numerics/bounds/m1_lean_data.py",
    }

    JSON_OUT.write_text(json.dumps(data, ensure_ascii=False, indent=1))
    print(f"[ok] 落盘 {JSON_OUT}  (B = {float(B):.9f}, bound_exact 逐位一致)")
    if not args.no_lean:
        emit_lean(data)
        print(f"[ok] 生成 {LEAN_OUT}")


# ================================================================ SOS 证书
def build_sos_certificate(P_u: list[Fr]) -> dict:
    """P(u) = Σ d0ᵢ·z0ᵢ(u)² + u·Σ d1ᵢ·z1ᵢ(u)²，z = LDLᵀ 列。"""
    import numpy as np
    import cvxpy as cp

    n = 8
    ntri = n * (n + 1) // 2
    nvar = 2 * ntri

    def sidx(w, i, j):
        a, b = min(i, j), max(i, j)
        base = 0 if w == 0 else ntri
        return base + b * (b + 1) // 2 + a

    rows, rhs = [], []
    for kd in range(16):
        row = [Fr(0)] * nvar
        for i in range(n):
            for j in range(n):
                if i + j == kd:
                    row[sidx(0, i, j)] += Fr(1)
                if i + j == kd - 1:
                    row[sidx(1, i, j)] += Fr(1)
        rows.append(row)
        rhs.append(P_u[kd])

    # 精确解 x0 + N y
    m = [r[:] + [v] for r, v in zip(rows, rhs)]
    piv = []
    r_ = 0
    for c in range(nvar):
        pr = next((rr for rr in range(r_, len(m)) if m[rr][c] != 0), None)
        if pr is None:
            continue
        m[r_], m[pr] = m[pr], m[r_]
        pv = m[r_][c]
        m[r_] = [x / pv for x in m[r_]]
        for rr in range(len(m)):
            if rr != r_ and m[rr][c] != 0:
                f = m[rr][c]
                m[rr] = [a - f * b for a, b in zip(m[rr], m[r_])]
        piv.append(c)
        r_ += 1
        if r_ == len(m):
            break
    assert r_ == 16, "方程组秩失配"
    x0 = [Fr(0)] * nvar
    for rr, c in enumerate(piv):
        x0[c] = m[rr][nvar]
    freecols = [c for c in range(nvar) if c not in piv]
    Nbasis = []
    for fc in freecols:
        v = [Fr(0)] * nvar
        v[fc] = Fr(1)
        for rr, c in enumerate(piv):
            v[c] = -m[rr][fc]
        Nbasis.append(v)
    kfree = len(Nbasis)

    # SDP（仅取初值；正确性全部由精确修复＋精确验证承担）
    G0 = cp.Variable((n, n), symmetric=True)
    G1 = cp.Variable((n, n), symmetric=True)
    cons = [G0 >> 0, G1 >> 0]
    for kd in range(16):
        e = 0
        for i in range(n):
            for j in range(n):
                if i + j == kd:
                    e += G0[i, j]
                if i + j == kd - 1:
                    e += G1[i, j]
        cons.append(e == float(P_u[kd]))
    tvar = cp.Variable()
    cons += [G0 - tvar * np.eye(n) >> 0, G1 - tvar * np.eye(n) >> 0]
    prob = cp.Problem(cp.Maximize(tvar), cons)
    prob.solve(solver=cp.CLARABEL)
    assert prob.status == "optimal", f"SDP 状态 {prob.status}"

    xf = np.array([float(v) for v in x0])
    Nf = np.array([[float(v) for v in row] for row in Nbasis]).T
    xstar = np.zeros(nvar)
    for a in range(n):
        for b in range(a, n):
            xstar[sidx(0, a, b)] = G0.value[a, b]
            xstar[sidx(1, a, b)] = G1.value[a, b]
    y_ls, *_ = np.linalg.lstsq(Nf, xstar - xf, rcond=None)

    def attempt(bits: int):
        yh = [Fr(int(round(float(v) * (1 << bits))), 1 << bits) for v in y_ls]
        x = [x0[i] + sum(Nbasis[r][i] * yh[r] for r in range(kfree)) for i in range(nvar)]
        mats = []
        for w in (0, 1):
            mats.append([[x[sidx(w, i, j)] for j in range(n)] for i in range(n)])
        # 线性恒等式（仿射结构保证精确成立）复核
        Pchk = [Fr(0)] * 16
        for i in range(n):
            for j in range(n):
                Pchk[i + j] += mats[0][i][j]
                if i + j + 1 < 16:
                    Pchk[i + j + 1] += mats[1][i][j]
        assert Pchk == list(P_u), "线性恒等式失配（不可能：仿射重参数化）"
        Ls, Ds = [], []
        for w in (0, 1):
            L, D = ldl_frac(mats[w])
            assert L is not None, f"bits={bits}: 块 {w} LDLᵀ 出现非正主元"
            Ls.append(L)
            Ds.append(D)
            # 复核 R = LDLᵀ
            chk = mat_mul_frac(mat_mul_frac(L, [[D[i] if i == j else Fr(0) for j in range(n)]
                                                for i in range(n)]),
                               [[L[j][i] for j in range(n)] for i in range(n)])
            assert chk == mats[w], "LDLᵀ 重乘失配"
        return Ls, Ds, min(Ds[0]), min(Ds[1])

    Ls = Ds = None
    for bits in (48, 40, 36, 32, 28, 24):
        try:
            Ls, Ds, m0, m1 = attempt(bits)
            used = bits
            break
        except AssertionError as e:
            print(f"[info] SDP 修复 bits={bits} 失败：{e}")
    assert Ls is not None, "所有舍入档位修复失败"

    # z 多项式（L 列）；验证 Σd·z² + u·Σd·z² == P 精确
    def zpolys(L):
        return [[L[j][i] for j in range(n)] for i in range(n)]   # z_i 的系数（按 u^j）
    Z0, Z1 = zpolys(Ls[0]), zpolys(Ls[1])
    lhs = [Fr(0)] * 16
    for i in range(n):
        sq = upoly_mul(Z0[i], Z0[i])
        for j, x in enumerate(sq):
            lhs[j] += Ds[0][i] * x
    for i in range(n):
        sq = upoly_mul(Z1[i], Z1[i])
        for j, x in enumerate(sq):
            if j + 1 < 16:
                lhs[j + 1] += Ds[1][i] * x
    upoly_trunc(lhs)
    assert lhs == list(P_u), "SOS 恒等式最终复核失配"

    return {"L0": Ls[0], "D0": Ds[0], "L1": Ls[1], "D1": Ds[1],
            "check": {"rounding_bits": used, "min_pivot_D0": str(m0),
                      "min_pivot_D1": str(m1),
                      "identity_exact": True, "psd_exact_ldlt": True,
                      "final_identity_verified": True}}


# ================================================================ 核机制
def build_kernel(k: int) -> dict:
    mons = tri_monomials(k)
    mon_idx = {mm: i for i, mm in enumerate(mons)}
    rows = []
    for m2 in (tri_monomials(k - 2) if k >= 2 else []):
        row = [Fr(0)] * len(mons)
        for d in range(3):
            src = list(m2)
            src[d] += 2
            si = mon_idx.get(tuple(src))
            if si is not None:
                row[si] += Fr(src[d] * (src[d] - 1))
        rows.append(row)
    ns = nullspace_frac(rows, len(mons))
    assert len(ns) == 2 * k + 1, f"k={k} dim={len(ns)}≠{2*k+1}"
    H = []
    for v in ns:
        den = 1
        for x in v:
            den = den * x.denominator // math.gcd(den, x.denominator)
        iv = [int(x * den) for x in v]
        g = 0
        for x in iv:
            g = math.gcd(g, abs(x))
        if g:
            iv = [x // g for x in iv]
        H.append({mons[i]: Fr(iv[i]) for i in range(len(mons)) if iv[i] != 0})
    # 二次调和审计
    for h in H:
        assert tri_laplacian(h) == {}, "基元非调和"
    R = gram_frac(H)
    n = 2 * k + 1
    Rinv = mat_inv_frac(R)
    assert mat_mul_frac(Rinv, R) == [[Fr(1) if i == j else Fr(0) for j in range(n)] for i in range(n)]
    L, D = ldl_frac(R)
    assert L is not None and all(d > 0 for d in D), "Gram LDLᵀ 非正"
    S = mat_inv_frac(L)

    # D_k = (2k+1)P_k(x·y) − Σ M_lj h_l(x) h_j(y)；归约得 A,B
    def dotpow(m):
        base = [(1, 0, 0, 1, 0, 0), (0, 1, 0, 0, 1, 0), (0, 0, 1, 0, 0, 1)]
        Rr = {(0,) * 6: Fr(1)}
        for _ in range(m):
            nxt = {}
            for kk, vv in Rr.items():
                for b in base:
                    key = tuple(kk[i] + b[i] for i in range(6))
                    nxt[key] = nxt.get(key, Fr(0)) + vv
            Rr = nxt
        return Rr
    D6 = {}
    Lk = legendre_mono(k)
    for e in range(len(Lk)):
        v = Lk[e]
        if v == 0:
            continue
        for kk, vv in dotpow(e).items():
            D6[kk] = D6.get(kk, Fr(0)) + v * vv * Fr(2 * k + 1)
    for l in range(n):
        for j in range(n):
            if Rinv[l][j] == 0:
                continue
            prod = hex_mul(lift_x(H[l]), lift_y(H[j]))
            D6 = hex_add(D6, hex_scale(prod, -Rinv[l][j]))
    D6 = {kk: vv for kk, vv in D6.items() if vv != 0}
    A, Bc = reduce_ideal(D6)
    # 恒等式复核
    X = {(2, 0, 0, 0, 0, 0): Fr(1), (0, 2, 0, 0, 0, 0): Fr(1), (0, 0, 2, 0, 0, 0): Fr(1),
         (0, 0, 0, 0, 0, 0): Fr(-1)}
    Y = {(0, 0, 0, 2, 0, 0): Fr(1), (0, 0, 0, 0, 2, 0): Fr(1), (0, 0, 0, 0, 0, 2): Fr(1),
         (0, 0, 0, 0, 0, 0): Fr(-1)}
    chk = hex_add(hex_add(hex_mul(X, A), hex_mul(Y, Bc)), hex_scale(D6, Fr(-1)))
    assert chk == {}, "球面恒等式复核失配"
    # 二次型复核（抽样 5 组整数向量）
    rng = random.Random(12345)
    for _ in range(5):
        vec = [Fr(rng.randint(-3, 3)) for _ in range(n)]
        lhsq = sum(Rinv[l][j] * vec[l] * vec[j] for l in range(n) for j in range(n))
        rhsq = sum(Fr(sum(S[i][l] * vec[l] for l in range(n))) ** 2 / D[i] for i in range(n))
        assert lhsq == rhsq, "二次型恒等式抽样失配"
    # 再生核球面点对复核（36 组）
    pts = [(Fr(1), Fr(0), Fr(0)), (Fr(0), Fr(1), Fr(0)), (Fr(0), Fr(0), Fr(1)),
           (Fr(3, 5), Fr(4, 5), Fr(0)), (Fr(2, 3), Fr(1, 3), Fr(2, 3)),
           (Fr(-1, 3), Fr(2, 3), Fr(2, 3))]
    for xpt in pts:
        assert sum(c * c for c in xpt) == 1
        for ypt in pts:
            def ev(h):
                return sum(v * xpt[0] ** e[0] * xpt[1] ** e[1] * xpt[2] ** e[2] for e, v in h.items())
            def evy(h):
                return sum(v * ypt[0] ** e[0] * ypt[1] ** e[1] * ypt[2] ** e[2] for e, v in h.items())
            t_ = sum(xpt[i] * ypt[i] for i in range(3))
            lhs = Fr(2 * k + 1) * sum(v * t_ ** j for j, v in enumerate(legendre_mono(k)))
            rhs = sum(Rinv[l][j] * ev(H[l]) * evy(H[j]) for l in range(n) for j in range(n))
            assert lhs == rhs, "再生核点对复核失配"
    return {
        "dim": n,
        "monomials": [list(mm) for mm in mons],
        "H": [[ {"".join(map(str, e)): str(v)} for e, v in h.items()] for h in H],
        "H_polys": [[[list(e), str(v)] for e, v in h.items()] for h in H],
        "R": [[str(x) for x in row] for row in R],
        "Rinv": [[str(x) for x in row] for row in Rinv],
        "L": [[str(x) for x in row] for row in L],
        "D": [str(x) for x in D],
        "S_Linv": [[str(x) for x in row] for row in S],
        "Dinv": [str(Fr(1) / d) for d in D],
        "Pk_mono": [str(x) for x in legendre_mono(k)],
        "A_terms": [[list(e), str(v)] for e, v in A.items()],
        "B_terms": [[list(e), str(v)] for e, v in Bc.items()],
        "D_terms": [[list(e), str(v)] for e, v in D6.items()],
        "checks": {"dim_ok": n == 2 * k + 1, "harmonic_ok": True,
                   "R_pd_ldlt_ok": True, "Rinv_ok": True,
                   "sphere_identity_exact": True,
                   "quadratic_sampled": True, "reproducing_kernel_36_pairs": True},
    }


# ================================================================ Lean 生成
def q_lit(v: Fr) -> str:
    """((num/den : ℚ) : ℝ) 字面量。"""
    if v == 0:
        return "((0 : ℚ) : ℝ)"
    num, den = v.numerator, v.denominator
    assert num != 0
    if den == 1:
        return f"(({num} : ℚ) : ℝ)" if num >= 0 else f"((-{-num} : ℚ) : ℝ)"
    return f"(({num}/{den} : ℚ) : ℝ)"

def z_lit(v: Fr) -> str:
    return q_lit(v)

def bal_join(parts, sep=" + "):
    """平衡二叉拼接（深度 log n，规避 simp 递归深度限制）。"""
    if not parts:
        return "((0 : ℚ) : ℝ)"
    if len(parts) == 1:
        return parts[0]
    mid = len(parts) // 2
    return f"({bal_join(parts[:mid], sep)}{sep}{bal_join(parts[mid:], sep)})"

def q_pure(v: Fr) -> str:
    """(n/d : ℚ) 纯 ℚ 字面量（矩阵用）。"""
    if v == 0:
        return "(0 : ℚ)"
    num, den = v.numerator, v.denominator
    if den == 1:
        return f"({num} : ℚ)" if num >= 0 else f"(-{-num} : ℚ)"
    return f"({num}/{den} : ℚ)"

def emit_lean(data: dict) -> None:
    L = []
    A = L.append
    A("import Mathlib")
    A("")
    A("/-!")
    A("# Thomson N=9, milestone M1 — generated rational data module")
    A("")
    A("Generated by `numerics/bounds/m1_lean_data.py` from `results/m1_lean_data.json`")
    A(f"(seed {SEED}; lp_m1_light sha256 {data['source_artifact']['sha256'][:16]}…).")
    A("Every constant below is an exact rational; all identities are proved by `ring` on")
    A("inline `((n / d : ℚ) : ℝ)` literals (coefficient arithmetic is numeric, GMP-backed).")
    A("")
    A("Contents:")
    A("* `fR` — the LP minorant f(t) = Σ c_k P_k(t) in the monomial basis (c_k from the")
    A("  frozen `lp_m1_light.json`, verbatim); `pR t = 1 - 2*(1-t)*(fR t)^2`.")
    A("* the nonnegativity certificate of p on [-1,1]: after the Möbius change of variable")
    A("  u = (1-t)/(1+t), the polynomial `PuR u = (1+u)^15 * pR ((1-u)/(1+u))` satisfies the")
    A("  half-line Lukács identity `PuR_nonneg` (sum of `d₀ᵢ·z₀ᵢ(u)² + u·d₁ᵢ·z₁ᵢ(u)²`, all")
    A("  d ≥ 0), so `PuR u ≥ 0` for u ≥ 0 and hence `pR t ≥ 0` on (-1,1]; `pR (−1) ≥ 0` directly.")
    A("  (The task's originally prescribed ℚ-factorisation of p is impossible: p is irreducible")
    A("  of odd degree over ℚ; see notes/m1-lean-data.md.)")
    A("* per k ∈ {1,2,3,7}: the harmonic basis `hK k _l`, the reproducing-kernel identity")
    A("  `sphereK k` ((2k+1)·P_k(x·y) = Σ M_lj·h_l(x)·h_j(y) on the sphere, via the ideal")
    A("  certificates A_k, B_k) and the quadratic form identity `quadK k` (M = R⁻¹ = SᵀD⁻¹S).")
    A("* assembly constants c₀,c₁,c₂,c₃,c₇, f(1), B = (81c₀ − 9f(1))/2 with `189/8 < B`.")
    A("-/")
    A("")
    A("namespace ThomsonN9.M1")
    A("")
    fd = data["f"]
    fmono = [Fr(x) for x in fd["monomial_coeffs"]]

    def polystr(var, coeffs):
        parts = []
        for j, c in enumerate(coeffs):
            if c == 0:
                continue
            if j == 0:
                parts.append(q_lit(c))
            elif j == 1:
                parts.append(f"{q_lit(c)} * {var}")
            else:
                parts.append(f"{q_lit(c)} * {var}^{j}")
        return " + ".join(parts) if parts else "((0 : ℚ) : ℝ)"
    A(f"noncomputable def fR (t : ℝ) : ℝ := {polystr('t', fmono)}")
    A("")
    A("/-- p t = 1 − f(t)²·(2−2t) — nonnegative on [-1,1] by the certificate below. -/")
    A("noncomputable def pR (t : ℝ) : ℝ := 1 - 2 * (1 - t) * (fR t)^2")
    A("")
    Pu = [Fr(x) for x in data["pos_certificate"]["moebius_P_coeffs"]]
    A(f"noncomputable def PuR (u : ℝ) : ℝ := {polystr('u', Pu)}")
    A("")
    # FM: (1+u)^15 * f((1-u)/(1+u)) 的清除分母形式
    fmparts = []
    for j, c in enumerate(fmono):
        if c == 0:
            continue
        if j == 0:
            fmparts.append(f"{q_lit(c)} * (1 + u)^15")
        else:
            fmparts.append(f"{q_lit(c)} * (1 - u)^{j} * (1 + u)^{15 - j}")
    A("/-- (1+u)^15 · f((1−u)/(1+u)) 的清分母多项式（度 15）。-/")
    A("noncomputable def FM (u : ℝ) : ℝ := " + (" + ".join(fmparts) if fmparts else "((0:ℚ):ℝ)"))
    A("")
    # Möbius identity
    A("/-- Möbius 变换恒等式（u ≠ −1）。-/")
    A("theorem moebius_id {u : ℝ} (hu : u ≠ -1) :")
    A("    (1 + u)^15 * pR ((1 - u)/(1 + u)) = PuR u := by")
    A("  have h1 : (1:ℝ) + u ≠ 0 := by")
    A("    intro h")
    A("    exact hu (by linarith)")
    A("  have hA : (1 + u)^15 * fR ((1 - u)/(1 + u)) = FM u := by")
    A("    unfold fR FM")
    A("    simp only [div_pow]")
    A("    field_simp")
    A("  have hC : fR ((1 - u)/(1 + u)) = FM u / (1 + u)^15 := by")
    A("    rw [eq_div_iff (pow_ne_zero 15 h1)]")
    A("    rw [mul_comm]")
    A("    exact hA")
    A("  have hB : 1 - (1 - u)/(1 + u) = 2 * u / (1 + u) := by")
    A("    field_simp")
    A("    ring")
    A("  unfold pR PuR")
    A("  rw [hB, hC]")
    A("  unfold FM")
    A("  field_simp")
    A("  push_cast")
    A("  ring")
    A("")
    # z polys
    pc = data["pos_certificate"]
    L0 = [[Fr(x) for x in row] for row in pc["L0"]]
    D0 = [Fr(x) for x in pc["D0"]]
    L1 = [[Fr(x) for x in row] for row in pc["L1"]]
    D1 = [Fr(x) for x in pc["D1"]]
    n = 8
    for w, (Lm, tag) in enumerate(((L0, "z0"), (L1, "z1"))):
        for i in range(n):
            coeffs = [Lm[j][i] for j in range(n)]
            A(f"noncomputable def {tag}_{i} (u : ℝ) : ℝ := {polystr('u', coeffs)}")
        A("")
    # certificate identity
    def sqterm(tag, i):
        return f"({tag}_{i} u)^2"
    lhs0 = " + ".join(f"{q_lit(D0[i])} * {sqterm('z0', i)}" for i in range(n) if D0[i] != 0)
    lhs1 = " + ".join(f"{q_lit(D1[i])} * {sqterm('z1', i)}" for i in range(n) if D1[i] != 0)
    A("/-- Lukács SOS 恒等式：PuR = Σ d0ᵢ·z0ᵢ² + u·Σ d1ᵢ·z1ᵢ²（精确）。-/")
    A("theorem PuR_cert (u : ℝ) :")
    A(f"    PuR u = ({lhs0}) + u * ({lhs1}) := by")
    zs = " ".join(f"z0_{i}" for i in range(n)) + " " + " ".join(f"z1_{i}" for i in range(n))
    A(f"  unfold PuR {zs}")
    A("  push_cast")
    A("  ring")
    A("")
    # nonneg
    A("/-- 半直线非负性：u ≥ 0 ⇒ PuR u ≥ 0（逐项平方×正系数）。-/")
    A("theorem PuR_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ PuR u := by")
    A("  rw [PuR_cert]")
    terms_nn = [f"{q_lit(D0[i])} * ({sqterm('z0', i)})" for i in range(n) if D0[i] != 0]
    inner_nn = [f"{q_lit(D1[i])} * ({sqterm('z1', i)})" for i in range(n) if D1[i] != 0]
    A(f"  have hu1 : 0 ≤ ({' + '.join(inner_nn)}) := by")
    for idx, tt in enumerate(inner_nn):
        A(f"    have hh{idx} : 0 ≤ {tt} := mul_nonneg (by push_cast; norm_num) (sq_nonneg _)")
    A(f"    exact {wrap_adds([f'hh{i}' for i in range(len(inner_nn))])}")
    A(f"  have hu0 : 0 ≤ ({' + '.join(terms_nn)}) := by")
    for idx, tt in enumerate(terms_nn):
        A(f"    have gg{idx} : 0 ≤ {tt} := mul_nonneg (by push_cast; norm_num) (sq_nonneg _)")
    A(f"    exact {wrap_adds([f'gg{i}' for i in range(len(terms_nn))])}")
    A("  exact add_nonneg hu0 (mul_nonneg hu hu1)")
    A("")
    A("/-- p(−1) ≥ 0（区间端点直接验证）。-/")
    A("theorem pR_m1_nonneg : 0 ≤ pR (-1) := by")
    A("  unfold pR fR")
    A("  push_cast")
    A("  norm_num")
    A("")
    # ---- kernels ----
    for k in KS:
        kd = data["kernels"][str(k)]
        nk = kd["dim"]
        Hpolys = [[[tuple(e), Fr(v)] for e, v in hp] for hp in kd["H_polys"]]
        Pk = [Fr(x) for x in kd["Pk_mono"]]
        Rinv = [[Fr(x) for x in row] for row in kd["Rinv"]]
        S = [[Fr(x) for x in row] for row in kd["S_Linv"]]
        Dinv = [Fr(x) for x in kd["Dinv"]]
        Aterms = [[tuple(e), Fr(v)] for e, v in kd["A_terms"]]
        Bterms = [[tuple(e), Fr(v)] for e, v in kd["B_terms"]]
        A(f"section K{k}")
        A(f"noncomputable def P{k}R (t : ℝ) : ℝ := {polystr('t', Pk)}")
        A("")
        for l, hp in enumerate(Hpolys):
            coeffs3 = {}
            for e, v in hp:
                coeffs3[tuple(e)] = v
            used = [any(e[0] > 0 for e in coeffs3), any(e[1] > 0 for e in coeffs3),
                    any(e[2] > 0 for e in coeffs3)]
            names = []
            for bi, bn in enumerate("abc"):
                names.append(bn if used[bi] else f"_{bn}")
            astr, bstr, cstr = names
            parts = []
            for (a, b, c), v in sorted(coeffs3.items()):
                mono = "*".join(s for s in ([astr] * a + [bstr] * b + [cstr] * c))
                parts.append(f"{q_lit(v)} * {mono}" if mono else q_lit(v))
            body = bal_join(parts) if parts else "((0 : ℚ) : ℝ)"
            A(f"noncomputable def h{k}_{l} ({astr} {bstr} {cstr} : ℝ) : ℝ := {body}")
        A("")
        def hexparts(terms):
            parts = []
            names = ["a", "b", "c", "d", "e", "g"]
            for e, v in sorted(terms):
                mono = "*".join(names[i] for i in range(6) for _ in range(e[i]))
                parts.append(f"{q_lit(v)} * {mono}" if mono else q_lit(v))
            return parts
        # Mflat：M-部分独立 def（镜像 Finset 展开项集，含零项）——使"求和求值"成为
        # 纯加法重排（abel），把多项式环恒等式留给 flat sphereK{k}（bal_join 浅树，已证快）。
        Mparts_all = [f"{q_lit(Rinv[l][j])} * (h{k}_{l} a b c) * (h{k}_{j} d e g)"
                      for l in range(nk) for j in range(nk)]
        A(f"/-- 再生核 M-部分（∑_{{l,j}} M_lj·h_l(x)·h_j(y) 的平坦镜像，零项保留）。-/")
        A(f"noncomputable def Mflat{k} (a b c d e g : ℝ) : ℝ := {bal_join(Mparts_all)}")
        A("")
        Mparts = [f"{q_lit(Rinv[l][j])} * (h{k}_{l} a b c) * (h{k}_{j} d e g)"
                  for l in range(nk) for j in range(nk) if Rinv[l][j] != 0]
        A(f"/-- 再生核球面恒等式（k={k}）：(‖x‖²−1)A+(‖y‖²−1)B 消项（精确多项式恒等式）。-/")
        A(f"theorem sphereK{k} (a b c d e g : ℝ) :")
        A(f"    ((2*{k}+1 : ℚ) : ℝ) * (P{k}R (a*d + b*e + c*g))")
        A(f"      = Mflat{k} a b c d e g")
        A(f"      + (a*a + b*b + c*c - 1) * ({bal_join(hexparts(Aterms))})")
        A(f"      + (d*d + e*e + g*g - 1) * ({bal_join(hexparts(Bterms))}) := by")
        hdefs = " ".join(f"h{k}_{l}" for l in range(nk))
        A(f"  unfold P{k}R Mflat{k} {hdefs}")
        A("  push_cast")
        A("  ring")
        A("")
        A("")
        # ---- 数值表（M 表供 Finset 求和求值；S/DI 以字面量内联进 quadK 族语句，
        #      规避 Matrix 字面量在 decide/norm_num 下对非 succ 形索引的求值卡死）----
        matR = "![%s]" % ", ".join("![%s]" % ", ".join(q_pure(x) for x in row) for row in Rinv)
        A(f"def M{k}R : Fin {nk} → Fin {nk} → ℚ :=")
        A(f"  {matR}")
        A("")
        # quadratic identity (flat, no Finset)
        q_parts = [f"{q_lit(Rinv[l][j])} * u {l} * u {j}"
                   for l in range(nk) for j in range(nk) if Rinv[l][j] != 0]
        q_parts_all = [f"{q_lit(Rinv[l][j])} * u {l} * u {j}"
                       for l in range(nk) for j in range(nk)]
        sq_parts = []
        for i in range(nk):
            lin = [f"{q_lit(S[i][l])} * u {l}" for l in range(nk) if S[i][l] != 0]
            if Dinv[i] != 0:
                sq_parts.append(f"{q_lit(Dinv[i])} * ({bal_join(lin) if lin else '((0:ℚ):ℝ)'})^2")
        A(f"/-- 二次型 M-部分平坦镜像（∑_{{l,j}} M_lj·u_l·u_j，零项保留）。-/")
        A(f"noncomputable def Qflat{k} (u : Fin {nk} → ℝ) : ℝ := {bal_join(q_parts_all)}")
        A("")
        A(f"/-- 二次型恒等式（k={k}）：uᵀR⁻¹u = Σ wᵢ²/Dᵢ（精确）。-/")
        A(f"theorem quadK{k} (u : Fin {nk} → ℝ) :")
        A(f"    Qflat{k} u = {' + '.join(sq_parts)} := by")
        A(f"  unfold Qflat{k}")
        A("  push_cast")
        A("  ring")
        A("")
        A(f"/-- 二次型非负（k={k}）：Dᵢ>0 逐项平方。-/")
        A(f"theorem quadK{k}_nonneg (u : Fin {nk} → ℝ) : 0 ≤ {' + '.join(sq_parts)} := by")
        for i in range(nk):
            if Dinv[i] != 0:
                A(f"  have q{i} : 0 ≤ {sq_parts[i]} := mul_nonneg (by push_cast; norm_num) (sq_nonneg _)")
        A(f"  exact {wrap_adds([f'q{i}' for i in range(nk) if Dinv[i] != 0])}")
        A("")
        A(f"theorem P{k}R_one : P{k}R 1 = 1 := by")
        A(f"  unfold P{k}R; push_cast; norm_num")
        A("")
        # ---- Finset 形式（供 Solution 组合）----
        htab = "![" + ", ".join(f"h{k}_{l}" for l in range(nk)) + "]"
        A(f"/-- H_k 基函数表。-/")
        A(f"noncomputable def h{k}T : Fin {nk} → ℝ → ℝ → ℝ → ℝ := {htab}")
        A("")
        A(f"/-- Finset 求和求值（k={k}）：∑∑ M h h = Mflat{k}（纯加法重排，abel）。-/")
        A(f"theorem hsumK{k} (a b c d e g : ℝ) :")
        A(f"    ∑ l, ∑ j, ((M{k}R l j : ℚ) : ℝ) * (h{k}T l a b c) * (h{k}T j d e g)")
        A(f"      = Mflat{k} a b c d e g := by")
        A(f"  simp only [Fin.sum_univ_castSucc, Fin.sum_univ_zero]")
        A(f"  simp only [M{k}R, h{k}T, Mflat{k}]")
        A("  abel")
        A("")
        # 大 k 的展开恒等式需要更高心跳预算（k=7：225 项＋A/B 修正 352 单项）
        A(f"/-- 再生核球面恒等式（k={k}，Finset 形式）。-/")
        A(f"theorem sphereK{k}S (a b c d e g : ℝ) :")
        A(f"    ((2*{k}+1 : ℚ) : ℝ) * (P{k}R (a*d + b*e + c*g))")
        A(f"      = ∑ l, ∑ j, ((M{k}R l j : ℚ) : ℝ) * (h{k}T l a b c) * (h{k}T j d e g)")
        A(f"      + (a*a + b*b + c*c - 1) * ({bal_join(hexparts(Aterms))})")
        A(f"      + (d*d + e*e + g*g - 1) * ({bal_join(hexparts(Bterms))}) := by")
        A(f"  rw [hsumK{k} a b c d e g]")
        A(f"  exact sphereK{k} a b c d e g")
        A("")
        lin_sqs = []
        for i in range(nk):
            lin_sqs.append([f"{q_lit(S[i][l])} * u {l}" for l in range(nk) if S[i][l] != 0])
        assert all(Dinv[i] != 0 for i in range(nk)), "Dinv 全正（LDLᵀ 主元为正）"
        A(f"/-- Finset 二次型求和求值（k={k}）：∑∑ M u u = Qflat{k}（纯加法重排，abel）。-/")
        A(f"theorem hsumQ{k} (u : Fin {nk} → ℝ) :")
        A(f"    ∑ l, ∑ j, ((M{k}R l j : ℚ) : ℝ) * u l * u j")
        A(f"      = Qflat{k} u := by")
        A(f"  simp only [Fin.sum_univ_castSucc, Fin.sum_univ_zero]")
        A(f"  simp only [M{k}R, Qflat{k}]")
        A("  abel")
        A("")
        A(f"/-- 二次型恒等式（k={k}，Finset 形式，RHS 平坦展开无求和号）。-/")
        A(f"theorem quadK{k}S (u : Fin {nk} → ℝ) :")
        A(f"    ∑ l, ∑ j, ((M{k}R l j : ℚ) : ℝ) * u l * u j")
        A(f"      = {' + '.join(f'{q_lit(Dinv[i])} * ({bal_join(lin_sqs[i])})^2' for i in range(nk))} := by")
        A(f"  rw [hsumQ{k} u]")
        A(f"  exact quadK{k} u")
        A("")
        A(f"end K{k}")
        A("")
    # ---- assembly ----
    asm = data["assembly"]
    A("-- ===== 装配常数 =====")
    for nm in ("c0", "c1", "c2", "c3", "c7"):
        A(f"noncomputable def {nm}R : ℝ := {q_lit(Fr(asm[nm]))}")
    A(f"noncomputable def fOneR : ℝ := {q_lit(Fr(asm['f_of_1']))}")
    A(f"noncomputable def BR : ℝ := {q_lit(Fr(asm['B']))}")
    A("")
    A("/-- f 的 Legendre 表示（P₀=1；P₄,₅,₆,₈ 系数为 0）。-/")
    A("theorem fR_eq_legendre (t : ℝ) :")
    A("    fR t = c0R + c1R * P1R t + c2R * P2R t + c3R * P3R t + c7R * P7R t := by")
    A("  unfold fR c0R c1R c2R c3R c7R P1R P2R P3R P7R")
    A("  push_cast")
    A("  ring")
    A("")
    A("theorem fR_one : fR 1 = fOneR := by")
    A("  unfold fR fOneR")
    A("  push_cast")
    A("  norm_num")
    A("")
    A("theorem B_assembly : (81 * c0R - 9 * fOneR) / 2 = BR := by")
    A("  unfold c0R fOneR BR")
    A("  push_cast")
    A("  ring")
    A("")
    A("theorem c1R_nonneg : 0 ≤ c1R := by unfold c1R; push_cast; norm_num")
    A("theorem c2R_nonneg : 0 ≤ c2R := by unfold c2R; push_cast; norm_num")
    A("theorem c3R_nonneg : 0 ≤ c3R := by unfold c3R; push_cast; norm_num")
    A("theorem c7R_nonneg : 0 ≤ c7R := by unfold c7R; push_cast; norm_num")
    A("")
    A("/-- 目标下界：189/8 < B = 25.728237201…（LP-light 装配值）。-/")
    A("theorem B_lower : (189 / 8 : ℝ) < BR := by")
    A("  unfold BR")
    A("  push_cast")
    A("  norm_num")
    A("")
    A("end ThomsonN9.M1")
    A("")
    LEAN_OUT.write_text("\n".join(L))

def wrap_adds(names, indent=0):
    """把 h0 h1 h2 … 组装成 add_nonneg 嵌套证明项（左结合，匹配 a+b+c 解析）。"""
    if not names:
        return "le_refl 0"
    expr = names[0]
    for nm in names[1:]:
        expr = f"add_nonneg ({expr}) {nm}"
    return expr


if __name__ == "__main__":
    main()
