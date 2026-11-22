#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""tube_analysis.py — 管状/稳定性量化：主战场 m ≥ −0.748 收尾的管半径 + typed 谱管重诊断。

GAP-REPORT Round 4 清单第 2 项（管状收尾的 typed 重诊断，在 m0748_M8 证书上重做
Round 2 endgame 组件 2/3）＋ 第 3 项的 Hessian 半部分（λ₊ 与管半径，含区间算术
严格版）。产出 results/tube.json。

## 口径

- **管半径（能量侧，L6 用）**：近 TTP 展开 E(X) ≈ E* + ½δᵀHδ。δ = 切向位移
  （9 点每点 2 个切向自由度，共 18 维），度量 = R²⁷ 弦距离 sqrt(Σᵢ‖δᵢ‖²)，
  **模掉 SO(3) 旋转轨道**（3 维旋转零模；D3h 有限重标号不影响特征值）。
  λ_min = 商空间（18−3 = 15 维本质切空间）上 Hessian 的最小特征值。
  ‖δ‖ ≲ sqrt(2·ΔE/λ_min)，ΔE = E* − certified(m0748_M8) = 4.153e-4（薄层厚度）。
  ⚠️ 二次增长只在 TTP 处的展开邻域内成立——本文件另给管内 λ_min 沿半径随机
  切向样本的扫描（数值证据）；全域严格版（27 维球上区间 Hessian）未开始。

- **谱管（Gram 侧，L2/L3/L4 用）**：typed 证书恒等式
  Σ_{84 类} λ_cls(x) + Σ_all(x) = E(x) − e   （精确恒等式，typed_ladder 自检）
  各项在域上 ≥ −R1_cls（R1 为 dyadic 舍入的认证折减）。故 E(x) ≤ E* 的竞争构型
  满足每类 λ_cls(x) ≤ ε_forcing := E* − e_dy + Σ_counts·R1 ≈ 4.15e-4。
  typed 相对 Round 2 untyped 的结构变化：504 项 → 84 项、轨道 10 → 3 条
  （AAA/AAB/ABC）；单项 ≤ 全和的放大从 ×504 型降到 ×1（每类独立 ≤ ε_forcing）。
  ρ_spec(ε) = 水平集 {λ_orbit ≤ ε} ∩ Gram 域 上"坐标到 TTP 6 节点谱最小距离"
  的最大值（Round 2 同口径，逐 orbit 分开）；需求 ρ_spec ≤ 半谱隙 ≈ 0.0185。

## 用法（thomson-n9 下）

  python3 numerics/bounds/tube_analysis.py                # 全流程（含扫描与区间）
  python3 numerics/bounds/tube_analysis.py --no-scan      # 跳过谱管扫描
  python3 numerics/bounds/tube_analysis.py --no-rigorous  # 跳过区间算术 λ_min
  python3 numerics/bounds/tube_analysis.py --n-grid 256   # 扫描网格（默认 512）
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
NUM = HERE.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(NUM))

from family import tri_cap_prism                    # noqa: E402
from energy import coulomb_energy                   # noqa: E402
from typed_ladder import QuotientMaps, load_E_star  # noqa: E402

CERT = HERE.parent.parent / "certificates" / "n9-stage-a4-typedcap-m0748_M8.json"
LADDER_RESULTS = HERE / "results" / "typed_ladder.json"
LOCAL_MIN = HERE / "results" / "local_min.json"
OUT = HERE / "results" / "tube.json"

A0 = Fraction(-187, 250)          # m0748 档切口
CAP_M, CAP_K = 8, 6               # m0748_M8 档
ORBITS = ("AAA", "AAB", "ABC")


def log(msg):
    print(msg, flush=True)


# ================================================================ TTP 几何
def ttp_state():
    """TTP 候选：z* Brent（cap_ladder.ttp_config 同路径）+ Gram 量。"""
    from scipy.optimize import minimize_scalar

    def fE(z):
        X = tri_cap_prism(z)
        d = np.linalg.norm(X[:, None, :] - X[None, :, :], axis=2)
        return float(np.sum(d[np.triu_indices(9, 1)] ** -1.0))

    res = minimize_scalar(fE, bounds=(0.4, 0.9), method="bounded",
                          options={"xatol": 1e-13})
    z = float(res.x)
    X = tri_cap_prism(z)
    G = X @ X.T
    t = np.sort(G[np.triu_indices(9, 1)])
    vals, counts = np.unique(np.round(t, 10), return_counts=True)
    return dict(z=z, X=X, E=fE(z), G=G, nodes=[float(v) for v in vals],
                multiplicities=[int(c) for c in counts],
                min_inner=float(t.min()),
                min_gap=float(np.min(np.diff(vals))))


# ================================================================ Hessian（数值）
def tangent_basis(X):
    """每点 2 个正交切向：e1 = ẑ×p/|ẑ×p|，e2 = p×e1。返回 (9,2,3)。"""
    bas = np.zeros((9, 2, 3))
    for i, p in enumerate(X):
        s = np.sqrt(p[0] ** 2 + p[1] ** 2)
        e1 = np.array([-p[1], p[0], 0.0]) / s
        e2 = np.cross(p, e1)
        bas[i, 0], bas[i, 1] = e1, e2
    return bas


def tangent_hessian(X):
    """切空间 Hessian B（18×18，切基坐标）+ λᵢ = ∇ᵢE·pᵢ。

    B 来自 Q(u) = Σ_{i<j}(uᵢ−uⱼ)ᵀ M̃_ij (uᵢ−uⱼ)，M̃_ij = 3r⁻⁵ddᵀ − r⁻³I
    （= ∂²(1/r)/∂x_i∂x_i 块，d = x_i−x_j），
    再减 Σᵢ λᵢ(uᵢ·vᵢ)（约束曲率项，标准 Lagrange 二阶条件）。
    """
    bas = tangent_basis(X)
    n = 9
    B = np.zeros((18, 18))
    lam = np.zeros(n)
    for i in range(n):
        g = np.zeros(3)
        for j in range(n):
            if i == j:
                continue
            d = X[i] - X[j]
            r = np.linalg.norm(d)
            g -= d / r ** 3
        lam[i] = float(g @ X[i])
    for i in range(n):
        for j in range(i + 1, n):
            d = X[i] - X[j]
            r = np.linalg.norm(d)
            M = 3.0 * r ** -5.0 * np.outer(d, d) - r ** -3.0 * np.eye(3)
            for si in range(2):
                for sj in range(2):
                    cii = bas[i, si] @ M @ bas[i, sj]
                    cjj = bas[j, si] @ M @ bas[j, sj]
                    cij = bas[i, si] @ M @ bas[j, sj]
                    B[2 * i + si, 2 * i + sj] += cii
                    B[2 * j + si, 2 * j + sj] += cjj
                    B[2 * i + si, 2 * j + sj] -= cij
                    B[2 * j + sj, 2 * i + si] -= cij
    for i in range(n):
        for si in range(2):
            B[2 * i + si, 2 * i + si] -= lam[i]
    return (B + B.T) / 2.0, bas, lam


def rotation_subspace(X, bas):
    """旋转轨道切向（axes x,y,z）在切基坐标下的 18×3 矩阵与 Gram。"""
    R = np.zeros((18, 3))
    for a, ax in enumerate(np.eye(3)):
        for i in range(9):
            v = np.cross(ax, X[i])
            R[2 * i, a] = v @ bas[i, 0]
            R[2 * i + 1, a] = v @ bas[i, 1]
    return R, R.T @ R


def geodesic_move(X, u, t):
    """构型沿切向场 u 的测地位移：速度范数 ‖u‖，参数 t。"""
    Y = np.zeros_like(X)
    for i in range(9):
        ni = np.linalg.norm(u[i])
        if ni == 0:
            Y[i] = X[i]
        else:
            th = ni * t
            Y[i] = X[i] * np.cos(th) + u[i] / ni * np.sin(th)
    return Y


def quotient_lambda_min(X):
    """(λ_min, 诊断) 在 15 维旋转补空间上。"""
    B, bas, lam = tangent_hessian(X)
    R, Rg = rotation_subspace(X, bas)
    Uq, _sq, _ = np.linalg.svd(R, full_matrices=True)
    comp = Uq[:, 3:]
    wq = np.linalg.eigvalsh(comp.T @ B @ comp)
    return float(wq[0]), dict(B=B, R=R, bas=bas, lam=lam, wq=wq)


def fd_check(X, B, trials=4, h=2e-4, seed=20261004):
    """测地线二阶差分 vs uᵀBu（随机单位切向 u；u 投影到切基坐标）。"""
    bas = tangent_basis(X)
    rng = np.random.default_rng(seed)
    rel = []
    for _ in range(trials):
        u = rng.standard_normal((9, 3))
        for i in range(9):
            u[i] -= (u[i] @ X[i]) * X[i]
        u /= np.linalg.norm(u)

        def E_at(t):
            return coulomb_energy(geodesic_move(X, u, t))

        E0 = E_at(0.0)
        fd = (E_at(h) - 2 * E0 + E_at(-h)) / h ** 2
        c = np.array([u[i] @ bas[i, s] for i in range(9) for s in range(2)])
        q = float(c @ B @ c)
        rel.append(dict(fd=fd, quad=q, rel=abs(fd - q) / max(abs(q), 1e-12)))
    return rel


def ball_lambda_scan(X, radii, n_dir=64, seed=20261005):
    """管内 λ_min 证据：随机切向位移到半径 r 的构型上重算商空间 λ_min。"""
    rng = np.random.default_rng(seed)
    out = {}
    for r in radii:
        vals = []
        for _ in range(n_dir):
            u = rng.standard_normal((9, 3))
            for i in range(9):
                u[i] -= (u[i] @ X[i]) * X[i]
            u /= np.linalg.norm(u)
            Y = geodesic_move(X, u, r)
            lamr, _ = quotient_lambda_min(Y)
            vals.append(lamr)
        out[f"r={r}"] = dict(min=float(np.min(vals)), mean=float(np.mean(vals)),
                             n=n_dir)
    return out


# ================================================================ 区间严格 λ_min
def rigorous_lambda_min(z_lo, z_hi, X_num=None, lambda_num=None,
                        mu_lo=0.10, mu_hi=0.16, dps=40,
                        penalty=10 ** 6, bisect=22):
    """区间算术严格下界：∀z∈[z_lo,z_hi]，∀切向 δ ⊥ 旋转场：δᵀH_zδ ≥ μ‖δ‖²。

    方法（deflation，15×15）：B(z)（18×18，代数项全区间）→ 区间 Gram–Schmidt
    构造 rot(z)⊥ 的 15 列区间正交基 N(z)（逐点正交归一）→ M = NᵀBN（15×15
    区间）→ 区间 LDLᵀ(M − μI) 全主元区间严格正 ⇒ ∀z：M(z) ≻ μI ⇒ 对
    δ ⊥ rot(z)，δ = N(z)c 给 δᵀBδ = cᵀM(z)c ≥ μ‖c‖² = μ‖δ‖²。
    μ 由二分寻最优。返回 (mu_cert, 诊断)；失败返回 (None, 诊断)。
    （早期罚项法 B+K·Π_rot 在 18×18 上因 1e5→0.14 的尺度悬殊抵消损失 ~3e-3，
    已弃用；开发过程中区间/数值 B 对拍与 μ₀<λ_num 卫语句各抓出过实现 bug。）

    自检：X_num 给定时，区间 B 在零宽中点 z 与数值 B（FD 复核过的公式）逐条
    对拍——本轮开发中该对拍抓出过赤道点 sin/cos 表两处错误。
    """
    import mpmath as mp
    mp.mp.dps = dps
    iv = mp.iv

    HALF = iv.mpf(1) / 2
    SQ3_2 = iv.sqrt(3) / 2

    def iconfig(z):
        """TTP 构型坐标区间（三角函数值全用精确代数常数）。"""
        rho = iv.sqrt(1 - z * z)
        c = [iv.mpf(1), iv.mpf(-1) / 2, iv.mpf(-1) / 2]
        s = [iv.mpf(0), SQ3_2, -SQ3_2]                     # sin(2πk/3)
        ce = [HALF, -iv.mpf(1), HALF]                     # cos(π/3+2πk/3)
        se = [SQ3_2, iv.mpf(0), -SQ3_2]                   # sin(π/3+2πk/3)
        P = []
        for k in range(3):
            P.append((rho * c[k], rho * s[k], z))
        for k in range(3):
            P.append((rho * c[k], rho * s[k], -z))
        for k in range(3):
            P.append((ce[k], se[k], iv.mpf(0)))
        return P

    def ibasis(P):
        bas = []
        for p in P:
            nxy = iv.sqrt(p[0] ** 2 + p[1] ** 2)
            e1 = (-p[1] / nxy, p[0] / nxy, iv.mpf(0))
            e2 = (p[1] * e1[2] - p[2] * e1[1],
                  p[2] * e1[0] - p[0] * e1[2],
                  p[0] * e1[1] - p[1] * e1[0])
            bas.append((e1, e2))
        return bas

    def dot(a, b):
        return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]

    zbox = iv.mpf(f"[{mp.mpf(str(z_lo))}, {mp.mpf(str(z_hi))}]")

    def mid(x):
        return (mp.mpf(x.a) + mp.mpf(x.b)) / 2

    def build_B(P, bas):
        """B(z)：Σ_{i<j}(uᵢ−uⱼ)ᵀM̃(uᵢ−uⱼ) − Σᵢλᵢ(uᵢ·vᵢ)（M̃ = 3r⁻⁵ddᵀ−r⁻³I）。"""
        B = [[iv.mpf(0)] * 18 for _ in range(18)]

        def bump(i, si, j, sj, c):
            B[2 * i + si][2 * j + sj] += c

        for i in range(9):
            for j in range(i + 1, 9):
                d = tuple(P[i][k] - P[j][k] for k in range(3))
                r2 = dot(d, d)
                r = iv.sqrt(r2)
                r3 = r ** 3

                def Mv(a, b):
                    # (aᵀ M̃ b) = (3(a·d)(d·b)/r² − a·b)/r³
                    return (3 * dot(a, d) * dot(d, b) / r2 - dot(a, b)) / r3

                for si in range(2):
                    for sj in range(2):
                        bump(i, si, i, sj, Mv(bas[i][si], bas[i][sj]))
                        bump(j, si, j, sj, Mv(bas[j][si], bas[j][sj]))
                        c = Mv(bas[i][si], bas[j][sj])
                        bump(i, si, j, sj, -c)
                        bump(j, sj, i, si, -c)
        # λᵢ = ∇ᵢE·pᵢ（∇ᵢE = −Σⱼ d_ij/r_ij³）
        for i in range(9):
            g = [iv.mpf(0)] * 3
            for j in range(9):
                if i == j:
                    continue
                d = tuple(P[i][k] - P[j][k] for k in range(3))
                r = iv.sqrt(dot(d, d))
                for k in range(3):
                    g[k] -= d[k] / r ** 3
            lam_i = dot(g, P[i])
            for si in range(2):
                bump(i, si, i, si, -lam_i)
        return B

    P = iconfig(zbox)
    bas = ibasis(P)
    B = build_B(P, bas)

    # ---- 与数值 B 的逐条对拍（自检，零宽中点 z；曾在开发中抓出赤道 sin/cos 表错误）----
    crosscheck = None
    if X_num is not None:
        zmid_fl = (float(str(z_lo)) + float(str(z_hi))) / 2
        X_mid = tri_cap_prism(zmid_fl)
        B_num, _bas_n, _lam_n = tangent_hessian(X_mid)
        zmid_iv = iv.mpf(repr(zmid_fl))
        P_mid = iconfig(zmid_iv)
        B_mid = build_B(P_mid, ibasis(P_mid))
        diff = max(abs(float(mid(B_mid[i][j])) - B_num[i, j])
                   for i in range(18) for j in range(18))
        crosscheck = dict(maxAbsDiffB=diff, passed=bool(diff < 1e-9),
                          z_mid=zmid_fl,
                          note="区间 B（零宽 z 中点）vs 数值 B（同 z，FD 复核公式）"
                               "逐条对拍")
        if diff >= 1e-9:
            return None, dict(error="区间/数值 B 对拍失败", **crosscheck)

    # ---- 旋转子空间区间 Gram–Schmidt + 补空间 15 列区间正交基 N ----
    # 逐点语义：对每个 z∈箱，N(z) 列正交归一且张成 rot(z)⊥（GS 的区间外壳
    # 逐点包含真值 GS），故 δ⊥rot(z) ⇔ ∃c: δ=N(z)c 且 ‖δ‖=‖c‖。
    axes = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    Rv = []
    for ax in axes:
        col = []
        for i in range(9):
            v = (ax[1] * P[i][2] - ax[2] * P[i][1],
                 ax[2] * P[i][0] - ax[0] * P[i][2],
                 ax[0] * P[i][1] - ax[1] * P[i][0])
            col.append((dot(v, bas[i][0]), dot(v, bas[i][1])))
        Rv.append(col)

    def ivec(col):
        return [col[i][k] for i in range(9) for k in range(2)]

    def gs_reduce(v, Qs):
        for q in Qs:
            dv = sum((q[i] * v[i] for i in range(18)), iv.mpf(0))
            v = [v[i] - dv * q[i] for i in range(18)]
        return v

    Qs = []
    for a in range(3):
        v = gs_reduce(ivec(Rv[a]), Qs)
        nrm = iv.sqrt(sum((v[i] ** 2 for i in range(18)), iv.mpf(0)))
        Qs.append([v[i] / nrm for i in range(18)])
    # 补空间：标准基向量依次 GS，残差范数下界 > 1/2 才收（决策对全箱一致）
    accepted, n_try = 0, 0
    comp_cols = []
    for e in range(18):
        if accepted == 15:
            break
        v0 = [iv.mpf(0)] * 18
        v0[e] = iv.mpf(1)
        v = gs_reduce(v0, Qs + comp_cols)
        nrm2 = sum((v[i] ** 2 for i in range(18)), iv.mpf(0))
        if float(mp.mpf(nrm2.a)) > 0.25:
            nrm = iv.sqrt(nrm2)
            comp_cols.append([v[i] / nrm for i in range(18)])
            accepted += 1
        n_try += 1
    if accepted != 15:
        return None, dict(error="补空间区间 GS 未取到 15 列", accepted=accepted)

    # ---- NᵀHN（15×15，区间）----
    n = 15
    Ht = [[sum((comp_cols[a][i] * B[i][j] * comp_cols[b][j]
                for i in range(18) for j in range(18)), iv.mpf(0))
           for b in range(n)] for a in range(n)]

    # 对称化（真值对称 ⇒ 交集仍包含真值）
    sym_fail = 0
    for i in range(n):
        for j in range(i + 1, n):
            lo_ = max(Ht[i][j].a, Ht[j][i].a)
            hi_ = min(Ht[i][j].b, Ht[j][i].b)
            if lo_ > hi_:
                sym_fail += 1
            else:
                Ht[i][j] = Ht[j][i] = iv.mpf((lo_, hi_))
    def _w(x):
        return mp.mpf(x.b) - mp.mpf(x.a)      # 零宽区间端点 → mpf

    width = max(_w(Ht[i][j]) for i in range(n) for j in range(n))
    maxabs = max(max(abs(mp.mpf(Ht[i][j].b)), abs(mp.mpf(Ht[i][j].a)))
                 for i in range(n) for j in range(n))
    if not mp.isfinite(maxabs):
        return None, dict(error="区间矩阵出现非有限条目", symFail=sym_fail)

    global _LAST_HT, _LAST_HT_W
    _LAST_HT = [[(float(mp.mpf(Ht[i][j].a)) + float(mp.mpf(Ht[i][j].b))) / 2
                 for j in range(n)] for i in range(n)]
    _LAST_HT_W = [[float(_w(Ht[i][j])) for j in range(n)] for i in range(n)]

    def chol_pd(mu):
        """区间 LDLᵀ：d_j = A_jj − Σ_{k<j} L_jk²·d_k；L_ij = (A_ij − Σ L_ik d_k
        L_jk)/d_j。全部主元区间严格正 ⇒ 箱内一切（对称）矩阵 PD。
        （开发中曾把 Cholesky 与 LDLᵀ 混写——d 当了除数又漏 d_k 因子——
        18×18 大动态范围下误判 PD；此版为标准 LDLᵀ。）"""
        A = [[Ht[i][j] - (mu if i == j else 0) for j in range(n)]
             for i in range(n)]
        D = [None] * n
        for j in range(n):
            d = A[j][j]
            for k in range(j):
                d = d - A[j][k] * D[k] * A[j][k]
            if not (d > 0):          # 要求整个区间严格正
                return False
            D[j] = d
            for i in range(j + 1, n):
                s = A[i][j]
                for k in range(j):
                    s = s - A[i][k] * D[k] * A[j][k]
                A[i][j] = s / d
        return True

    lo, hi = float(mu_lo), float(mu_hi)
    if not chol_pd(iv.mpf(repr(lo))):
        found = False
        for start in (0.08, 0.05, 0.02, 0.01, 0.005, 0.0):
            if chol_pd(iv.mpf(repr(start))):
                lo, found = start, True
                break
        if not found:
            return None, dict(error="区间 LDLᵀ 在 μ=0 未过",
                              maxWidth=float(width), symFail=sym_fail)
    # 上 bracket：若 hi 也能认证则抬 lo 并扩 hi；否则 hi 维持为失败上界
    guard_hi = (lambda_num * 1.02 + 1e-3) if lambda_num else 2.0
    hi = min(max(float(mu_hi), lo * 1.05), guard_hi)
    while chol_pd(iv.mpf(repr(hi))) and hi < guard_hi:
        lo = hi
        hi = min(hi * 1.3, guard_hi)
    n_ok = 0
    for _ in range(bisect):
        mu_mid = (lo + hi) / 2
        if chol_pd(iv.mpf(repr(mu_mid))):
            lo, n_ok = mu_mid, n_ok + 1
        else:
            hi = mu_mid
    out = dict(bisect_ok=n_ok, bisect_total=bisect, maxWidth=float(width),
               maxAbsEntry=float(maxabs), dps=dps,
               method="deflation：区间 GS 15 列补基 N + 15×15 区间 LDLᵀ",
               claim="μ*：∀z∈严格 z-箱 ∀切向δ⊥旋转场 δᵀH_zδ ≥ μ‖δ‖²；"
                     "依据＝N(z) 逐点正交归一张成 rot(z)⊥ + 区间 LDLᵀ 全主元"
                     "区间严格正 ⇒ N(z)ᵀB(z)N(z) ≻ μI",
               assumptions=["local_min.json z-箱（区间算术严格）",
                            "约束流形 Hessian 公式（教科书二阶条件；"
                            "数值侧 FD 交叉复核 + 区间/数值 B 对拍）",
                            "mpmath.iv 区间算术正确性"])
    if crosscheck is not None:
        out["crosscheck"] = crosscheck
    if lambda_num is not None and lo > guard_hi:
        return None, dict(error="严格 μ₀ 超过卫语句上界（不可能，链有误）",
                          mu=lo, lambda_num=lambda_num, **out)
    return lo, out


def rigorous_lambda_min_boxed(z_lo, z_hi, X_num=None, lambda_num=None,
                              k_list=(8, 32, 128), dps=40, bisect=18):
    """真 z-箱上的严格 λ_min：子箱分裂控制区间包裹（宽度线性缩小）。

    对每个 K ∈ k_list：把 [z_lo,z_hi] 等分 K 份，逐份跑单箱 deflation 认证
    （成功取该份的 μ），全份成功 ⇒ μ_K = min 份内 μ。取第一个达到
    μ ≥ 0.9·λ_num（或跑完 k_list）的 K。返回 (mu, 诊断)。
    """
    t0 = time.time()
    zl, zh = mp_frac(z_lo), mp_frac(z_hi)
    sub0 = {}
    for K in k_list:
        mus, widths = [], []
        ok = True
        for s in range(K):
            a = zl + (zh - zl) * Fraction(s, K)
            b = zl + (zh - zl) * Fraction(s + 1, K)
            mu, diag = rigorous_lambda_min(_frac_str(a), _frac_str(b),
                                           X_num=X_num if s == 0 else None,
                                           lambda_num=None, dps=dps,
                                           bisect=bisect)
            if mu is None:
                return None, dict(error=f"子箱 {s}/{K} 认证失败", sub=diag)
            if s == 0:
                sub0 = diag
            mus.append(mu)
            widths.append(diag.get("maxWidth"))
        mu_min = min(mus)
        out = dict(K=K, sub_mu_min=mu_min, sub_mu_max=max(mus),
                   sub_maxWidth=max(widths),
                   runtime_s=round(time.time() - t0, 1))
        for key in ("claim", "assumptions", "method"):
            if key in sub0:
                out[key] = sub0[key]
        if "crosscheck" in sub0:
            out["crosscheck"] = sub0["crosscheck"]
        if lambda_num is not None and mu_min >= 0.9 * lambda_num:
            out["converged"] = f"K={K} 达 0.9·λ_num"
            return mu_min, out
    out["converged"] = f"k_list 用尽，K={k_list[-1]}（μ={mu_min:.6f}）"
    return mu_min, out


def mp_frac(x):
    return Fraction(str(x))


def _frac_str(fr):
    """Fraction → 可被 mp.mpf 接受的十进制串（截 60 位足够）。"""
    n = fr.numerator
    d = fr.denominator
    # 长除法取 60 位小数
    digits = []
    r = n % d
    q = n // d
    for _ in range(60):
        r *= 10
        digits.append(str(r // d))
        r %= d
    return f"{q}.{'' .join(digits)}"


# ================================================================ typed slack
def load_cert_data():
    with open(CERT) as f:
        cert = json.load(f)
    b = cert["blocks"]
    data = dict(
        h_AA=[Fraction(s) for s in b["h_AA_diag"]],
        h_AB=[Fraction(s) for s in b["h_AB_diag"]],
        psi_AA=[Fraction(s) for s in b["psi_AA_diag"]],
        psi_AB=[Fraction(s) for s in b["psi_AB_diag"]],
        c_A=Fraction(b["c_A"][0]), c_B=Fraction(b["c_B"][0]),
        c_C=Fraction(b["c_C"][0]), e=Fraction(b["e"][0]),
        F=[[[Fraction(s) for s in row] for row in b[f"F{k}"]]
           for k in range(CAP_K)],
    )
    return cert, data


def lam_tensors(qm, data):
    """三个轨道 λ 的系数张量（float，(15,15,15)）。"""
    out = {}
    for orbit in ORBITS:
        cvec = qm.lam(orbit, data)
        C = np.zeros((qm.D + 1, qm.D + 1, qm.D + 1))
        for q, e in enumerate(qm.ring.mons):
            C[e[0], e[1], e[2]] += float(cvec[q])
        out[orbit] = C
    return out


def class_triples_and_eval(qm, data, st):
    """TTP 的 84 类三元组（每 3-子集一次）+ 各类 λ 值。

    槽序（与 typed_ladder.full_classes 的机器核对一致）：
    类 (X,Y,Z)（块号 X≤Y≤Z），u = ⟨p_X p_Y⟩、v = ⟨p_X p_Z⟩、t = ⟨p_Y p_Z⟩；
    perm = u↔t 当 Y==Z≠X。同类内按指标升序取点。
    """
    G = st["G"]
    blocks = [(0, 1, 2), (3, 4, 5), (6, 7, 8)]        # A=top, B=bottom, C=eq
    lam_orbit = {o: qm.lam(o, data) for o in ORBITS}
    lam_cls = {}
    for (cls, orbit, perm_id) in qm.full_classes:
        lv = lam_orbit[orbit]
        lam_cls[cls] = lv if perm_id == "id" else qm.ring.swap_ut(lv)

    def trip(u, v, t):
        return (Fraction(u).limit_denominator(10 ** 15),
                Fraction(v).limit_denominator(10 ** 15),
                Fraction(t).limit_denominator(10 ** 15))

    res = []
    tot = Fraction(0)
    per_orbit = {o: {"values": [], "triples": []} for o in ORBITS}
    for Xb in range(3):
        for Yb in range(Xb, 3):
            for Zb in range(Yb, 3):
                cls = (Xb, Yb, Zb)
                orbit = ("AAA" if Xb == Yb == Zb
                         else ("ABC" if Xb < Yb < Zb else "AAB"))
                lv = lam_cls[cls]
                if Xb == Yb == Zb:
                    it = [tuple(blocks[Xb])]          # C(3,3)=1
                elif Xb == Yb:
                    it = [(i, j, l) for a, i in enumerate(blocks[Xb])
                          for j in blocks[Xb][a + 1:] for l in blocks[Zb]]
                elif Yb == Zb:
                    it = [(i, j, l) for i in blocks[Xb]
                          for a, j in enumerate(blocks[Yb])
                          for l in blocks[Yb][a + 1:]]
                else:
                    it = [(i, j, l) for i in blocks[Xb] for j in blocks[Yb]
                          for l in blocks[Zb]]
                for (i, j, l) in it:
                    u, v, t = trip(G[i, j], G[i, l], G[j, l])
                    val = qm.ring.eval3(lv, u, v, t)
                    counts = {"AAA": 1, "AAB": 9, "ABC": 27}[orbit]
                    tot += val
                    per_orbit[orbit]["values"].append(float(val))
                    per_orbit[orbit]["triples"].append((float(u), float(v), float(t)))
                    res.append(dict(cls=cls, orbit=orbit, value=float(val),
                                    counts=counts))
    assert len(res) == 84, len(res)
    return res, tot, per_orbit


def lambda_grad_hess(C, tau, h=1e-5):
    """λ 在 τ=(u,v,t) 的梯度与 Hessian（中心差分）。"""
    def f(p):
        return float(np.einsum("i,j,k,ijk->",
                               p[0] ** np.arange(C.shape[0]),
                               p[1] ** np.arange(C.shape[1]),
                               p[2] ** np.arange(C.shape[2]), C))

    tau = np.asarray(tau, dtype=float)
    g = np.zeros(3)
    H = np.zeros((3, 3))
    for k in range(3):
        e = np.zeros(3)
        e[k] = h
        g[k] = (f(tau + e) - f(tau - e)) / (2 * h)
        for m in range(k, 3):
            em = np.zeros(3)
            em[m] = h
            d2 = (f(tau + e + em) - f(tau + e - em)
                  - f(tau - e + em) + f(tau - e - em)) / (4 * h * h)
            H[k, m] = H[m, k] = d2
    return g, H


# ================================================================ 谱管扫描
def scan_orbit(C, a_fl, nodes, ttp_triples, eps_list, n_grid):
    """均匀网格扫描：{λ≤ε}∩Gram 域 的 ρ_spec/ρ_∞/轴投影。

    ρ_spec = 点到 6 节点谱的逐坐标最小距离的最大值（取三坐标最差）；
    ρ_∞ = 到 TTP 本轨道三元组集（去重）的 L∞ 距离最大值。
    距离函数 1-Lipschitz ⇒ ρ_true ≤ ρ_grid + √3·h（分辨率 h 报出）。
    """
    D = C.shape[0] - 1
    g = np.linspace(a_fl, 1.0, n_grid)
    h = float(g[1] - g[0])
    dnode = np.min(np.abs(g[:, None] - np.asarray(nodes)[None, :]), axis=1)
    tset = np.unique(np.round(np.asarray(ttp_triples), 9), axis=0)
    V = g[:, None] ** np.arange(D + 1)[None, :]

    res = {eps: dict(rho_spec=-1.0, rho_inf=-1.0, n=0, worst=None, worst_spec=None)
           for eps in eps_list}
    proj = {eps: np.zeros((3, n_grid), dtype=bool) for eps in eps_list}
    min_global = np.inf
    for iu, u in enumerate(g):
        Cu = np.zeros((D + 1, D + 1))
        for a in range(D + 1):
            Cu += (u ** a) * C[a]
        lam = V @ Cu @ V.T                                    # (n,n) λ(u,v,t)
        det = (1 - u * u - g[:, None] ** 2 - g[None, :] ** 2
               + 2 * u * np.outer(g, g))
        lam = np.where(det >= 0.0, lam, np.inf)
        if np.isfinite(lam).any():
            min_global = min(min_global, float(np.min(lam)))
        dspec_pt = np.maximum(np.maximum(dnode[iu], dnode[:, None]), dnode[None, :])
        dinf_pt = np.full(lam.shape, np.inf)
        for tau in tset:
            dd = np.maximum(np.maximum(np.abs(u - tau[0]),
                                       np.abs(g[:, None] - tau[1])),
                            np.abs(g[None, :] - tau[2]))
            dinf_pt = np.minimum(dinf_pt, dd)
        for eps in eps_list:
            m = lam <= eps
            if not m.any():
                continue
            r = res[eps]
            r["n"] += int(m.sum())
            ds = float(dspec_pt[m].max())
            di = float(dinf_pt[m].max())
            if ds > r["rho_spec"]:
                r["rho_spec"] = ds
                ii, jj = np.argwhere(m & (dspec_pt >= ds - 1e-12))[0]
                r["worst_spec"] = [float(u), float(g[ii]), float(g[jj])]
            if di > r["rho_inf"]:
                r["rho_inf"] = di
                ii, jj = np.argwhere(m & (dinf_pt >= di - 1e-12))[0]
                r["worst"] = [float(u), float(g[ii]), float(g[jj])]
            proj[eps][0, iu] |= bool(m.any())
            proj[eps][1] |= m.any(axis=1)
            proj[eps][2] |= m.any(axis=0)
    axes = {}
    for eps in eps_list:
        info = {}
        for ax in range(3):
            mask = proj[eps][ax]
            S = g[mask]
            info[f"axis{'uvt'[ax]}"] = dict(
                covered=int(mask.sum()),
                tube_radius=(float(np.max(dnode[mask])) if mask.any() else None),
                lo_hi=([float(S[0]), float(S[-1])] if len(S) else None))
        axes[repr(eps)] = info
    return res, axes, h, float(min_global)


# ================================================================ main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-scan", action="store_true")
    ap.add_argument("--no-rigorous", action="store_true")
    ap.add_argument("--no-ball", action="store_true")
    ap.add_argument("--n-grid", type=int, default=512)
    ap.add_argument("--out", type=Path, default=OUT)
    args = ap.parse_args()
    t0 = time.time()

    E_star_f = load_E_star()
    E_star = float(E_star_f)
    with open(LADDER_RESULTS) as f:
        ladder = json.load(f)
    rung = next(r for r in ladder["rungs"] if r["tag"] == "m0748" and r["M"] == 8)
    certified = Fraction(rung["certified"])
    certified_f = float(rung["certified_float"])
    delta_E = float(E_star_f - certified)      # 薄层厚度
    log(f"[meta ] E* = {E_star:.9f}  certified(m0748_M8) = {certified_f:.12f}  "
        f"ΔE = {delta_E:.6e}")

    # ---------------- TTP 几何 ----------------
    st = ttp_state()
    half_gap = st["min_gap"] / 2
    log(f"[ttp  ] z* = {st['z']:.13f}  E(z*) = {st['E']:.12f}")
    log(f"[ttp  ] nodes = {st['nodes']}  重数 = {st['multiplicities']}")
    log(f"[ttp  ] min_gap = {st['min_gap']:.6f}  half_gap(谱管需求) = {half_gap:.6f}")

    # ---------------- Hessian 数值 ----------------
    B, bas, lam_mult = tangent_hessian(st["X"])
    R, Rg = rotation_subspace(st["X"], bas)
    w = np.linalg.eigvalsh(B)
    Uq, _sq, _ = np.linalg.svd(R, full_matrices=True)
    comp = Uq[:, 3:]
    wq = np.linalg.eigvalsh(comp.T @ B @ comp)
    lambda_min = float(wq[0])
    resid_rot = float(np.linalg.norm(B @ R))
    ang = float(np.linalg.norm(R.T @ comp))
    fd = fd_check(st["X"], B)
    log(f"[hess ] 18 维谱最小 5 个 = {np.round(w[:5], 8)}")
    log(f"[hess ] λ_min(商空间 15 维) = {lambda_min:.6f}；‖BR‖ = {resid_rot:.2e}；"
        f"‖Rᵀ·comp‖ = {ang:.2e}")
    log(f"[hess ] FD 复核（4 方向）：相对偏差 = "
        f"{['%.2e' % r['rel'] for r in fd]}")
    tube_r = float(np.sqrt(2 * delta_E / lambda_min))
    log(f"[tube ] r_tube = sqrt(2·{delta_E:.4e}/{lambda_min:.6f}) = {tube_r:.6f}")

    ball = None
    if not args.no_ball:
        log("[ball ] 管内 λ_min 随机方向扫描（数值证据）…")
        ball = ball_lambda_scan(st["X"], [0.02, 0.04, round(tube_r, 4)])
        for k, v in ball.items():
            log(f"[ball ] {k}: λ_min min = {v['min']:.6f} (n={v['n']})")

    # ---------------- 区间严格 λ_min ----------------
    rig = None
    if not args.no_rigorous:
        with open(LOCAL_MIN) as f:
            lm = json.load(f)
        zl, zh = lm["zStarIntervalMpmath"].strip("[]").split(", ")
        log(f"[rig  ] z-箱（local_min.json 严格区间）宽 = "
            f"{float(Fraction(zh) - Fraction(zl)):.3e}")
        mu, diag = rigorous_lambda_min_boxed(zl, zh, X_num=st["X"],
                                             lambda_num=lambda_min)
        if mu is None:
            log(f"[rig  ] 失败：{diag}")
        else:
            rig_r = float(np.sqrt(2 * delta_E / mu))
            log(f"[rig  ] μ₀ = {mu:.6f} ⇒ 严格管半径 ≤ sqrt(2ΔE/μ₀) = {rig_r:.6f}")
            rig = dict(mu0=mu, radius=rig_r, **{k: v for k, v in diag.items()
                                                if k != "error"})
            # 并行工作流 full_local_min.py 的独立区间证书（含临界性，更强）——
            # 双实现交叉验证 + 链上取强
            flm_path = HERE / "results" / "full_local_min.json"
            if flm_path.exists():
                with open(flm_path) as f:
                    flm = json.load(f)
                lam_f = float(flm["lambdaCertifiedLowerBound"])
                consistent = (mu <= lam_f + 1e-12
                              and lam_f <= lambda_min + 5e-4)
                rig["cross_workstream"] = dict(
                    source="numerics/bounds/full_local_min.py（commit 6ef9647，"
                           "含临界性 L1–L3 的全空间严格局部极小区间证书）",
                    lambda_min_certified=lam_f,
                    consistent=bool(consistent),
                    note=f"两个独立区间实现一致：本文件 μ₀={mu:.6f}（deflation+区间"
                         f"LDLᵀ，仅 Hessian 二次型口径）≤ full_local_min "
                         f"{lam_f:.8f}（中值形式+预条件同余，含临界性）≤ 数值 "
                         f"{lambda_min:.6f}；引理链 L6 取强者 {lam_f:.8f}，"
                         f"对应管半径 sqrt(2ΔE/λ) = "
                         f"{float(np.sqrt(2 * delta_E / lam_f)):.5f}")
                log(f"[rig  ] 交叉验证 full_local_min λ_min ≥ {lam_f:.8f}：一致 = "
                    f"{consistent}（链上半径 = "
                    f"{float(np.sqrt(2 * delta_E / lam_f)):.5f}）")

    # ---------------- typed slack ----------------
    cert, data = load_cert_data()
    qm = QuotientMaps(A0, CAP_M, CAP_K)
    e_dy = data["e"]
    res_cls, tot84, per_orbit = class_triples_and_eval(qm, data, st)
    E_minus_e = float(E_star_f - e_dy)
    ok_ident = float(tot84) <= E_minus_e + 1e-12
    log(f"[slack] E* − e_dy = {E_minus_e:.6e}；Σ_84 λ_cls(TTP) = {float(tot84):.6e}"
        f"（≤ 上者：{ok_ident}）")
    for o in ORBITS:
        vv = per_orbit[o]["values"]
        log(f"[slack] {o}: n = {len(vv)}  max = {max(vv):.3e}  "
            f"min = {min(vv):.3e}  mean = {float(np.mean(vv)):.3e}")
    # ε_forcing（诚实口径）：
    #   恒等式 Σ_cls λ_cls + Σ_all = E − e_dy，λ_cls ≥ −R1_orbit，Σ_all ≥ 0
    #   ⇒ λ_cls ≤ (E* − e_dy) + Σ_{cls'≠cls} R1_{orbit'}
    #     ≤ (E* − e_dy) + Σ_counts·R1（认证 deflation 同口径，偏保守）
    R1 = rung["R1"]
    R2max = rung["R2max"]
    counts_w = {"AAA": 3 * 1, "AAB": 6 * 9, "ABC": 1 * 27}
    R1_sum = sum(counts_w[o] * float(R1[o]) for o in R1)
    eps_forcing = E_minus_e + R1_sum
    log(f"[force] ε_forcing = E*−e_dy + Σ_counts·R1 = {E_minus_e:.4e} + "
        f"{R1_sum:.3e} = {eps_forcing:.4e}（R2 因子 ≤ {R2max:.1e} 忽略级）")
    eps_ttp = max(max(per_orbit[o]["values"]) for o in ORBITS)
    log(f"[force] TTP 自身 slack 水平（84 类最大）= {eps_ttp:.4e}")

    tensors = lam_tensors(qm, data)
    local_model = {}
    for o in ORBITS:
        vv = per_orbit[o]["values"]
        tr = per_orbit[o]["triples"]
        k = int(np.argmax(vv))
        g_, H_ = lambda_grad_hess(tensors[o], tr[k])
        ev = np.linalg.eigvalsh(H_)
        local_model[o] = dict(tau=tr[k], lam=float(vv[k]),
                              grad=[float(x) for x in g_],
                              grad_norm=float(np.linalg.norm(g_)),
                              hess_eig=[float(x) for x in ev])
        log(f"[local] {o}: λ(τ) = {vv[k]:.3e}  |∇λ| = {np.linalg.norm(g_):.3e}  "
            f"λ-Hess 谱 = {np.round(ev, 5)}")

    # ---------------- 谱管扫描 ----------------
    scan = None
    eps_list = sorted({eps_forcing, 3e-4, 1e-4, 2e-5, eps_ttp, 1e-7, 1.5e-8})
    if not args.no_scan:
        log(f"[scan ] ε 列表 = {['%.3e' % e for e in eps_list]}  "
            f"n_grid = {args.n_grid}")
        scan = {}
        for o in ORBITS:
            res_o, axes_o, h_g, min_sl = scan_orbit(
                tensors[o], float(A0), st["nodes"], per_orbit[o]["triples"],
                eps_list, args.n_grid)
            scan[o] = dict(res={repr(e): res_o[e] for e in eps_list},
                           axes=axes_o, grid_h=h_g, min_slack=min_sl)
            log(f"[scan ] {o}: 全域 min λ = {min_sl:.3e}（负深度=残差指示）")
            for e in eps_list:
                r = res_o[e]
                log(f"[scan ]   ε={e:.2e}: ρ_spec = {r['rho_spec']:.5f}  "
                    f"ρ_∞ = {r['rho_inf']:.5f}  点数 = {r['n']}")
            log(f"[scan ]   分辨率 h = {h_g:.2e} ⇒ ρ_true ≤ ρ_grid+√3h = "
                f"{np.sqrt(3) * h_g:.5f}")

    # ---------------- verdict：瓶颈判断 ----------------
    verdict = dict(need=half_gap)
    if scan:
        eps_floor = 1.5e-8           # 刚过全域 min λ（≈9.4e-9 残差水平）
        worst_f = max(scan[o]["res"][repr(eps_forcing)]["rho_spec"] for o in scan)
        worst_0 = max(scan[o]["res"][repr(eps_floor)]["rho_spec"] for o in scan)
        plateau = max(scan[o]["res"][repr(eps_ttp)]["rho_spec"] for o in scan)
        verdict.update(
            rho_spec_at_forcing=worst_f, ratio_at_forcing=worst_f / half_gap,
            rho_spec_at_ttp_level=plateau, ratio_at_ttp_level=plateau / half_gap,
            rho_spec_at_floor=worst_0, ratio_at_floor=worst_0 / half_gap,
            bottleneck=(
                "slack 零集几何（L3）。ρ_spec 阶梯（三 orbit 一致）：ε=1.5e-8 → "
                f"{worst_0:.4f}（差 {worst_0 / half_gap:.1f}×；全网最深点 "
                "(0.1961,0.1961,0.1961) 为三轨道共同的伪近零/最深点，深度 9.4e-9 "
                "与 R1 残差同级——可能是 SOS 族真零点，非舍入假象可排除）；"
                "1e-7 → 0.1043（5.6×）；5.3e-6~1e-4 → 0.2548 平台（TTP 自身 "
                f"slack 水平即差 {plateau / half_gap:.0f}×）；≥3e-4 → 0.6447 平台"
                f"（ε_forcing=4.15e-4 所在，差 {worst_f / half_gap:.0f}×）。"
                "a₀=−0.7476 只把 ε 压到 ~3.7e-4——与 ε_forcing 同在 0.6447 平台，"
                "ρ_spec 零变化 ⇒ 追加 cap 解对 L3 零收益、对 L1 拼合界 ~1e-4 级，"
                "不动用"),
            round2_comparison=("同口径 ρ_spec(ε=2e-5)：Round 2 untyped (8,6)@−0.755 "
                               "实测 0.0755（域 [−0.755,1]）vs 本轮 typed (8,6)@−0.748 "
                               f"实测 {plateau:.4f}（域 [−0.748,1]）——typed 把界贴近 "
                               "E*（4.15e-4）但 slack 水平集反而更胖：贴界 ≠ 零集局部"
                               "化，两者由 SOS 结构不同侧面决定（定性对比，证书与域"
                               "都不同）"),
            relaxation_note=("扫描是逐三元组松弛：每类 λ ≤ ε 是必要条件；84 类联合 +"
                             " Gram 全局一致性（秩 3/单位对角）未被利用——路线 b 的"
                             "管状证书正是要在联合层面重新构造"),
        )
        log(f"[verd ] ρ_spec: ε_forcing {worst_f:.4f} / TTP 水平 {plateau:.4f} / "
            f"零集地板 {worst_0:.4f} vs 需求 {half_gap:.5f}"
            f"（差 {worst_0 / half_gap:.0f}–{worst_f / half_gap:.0f} 倍）")
        log("[verd ] 瓶颈 = slack 零集几何（非薄层厚度）⇒ 不动用 a₀=−0.7476 追加解")

    # ---------------- lemma design / routes ----------------
    lemma_design = build_lemma_design(delta_E, lambda_min, tube_r, rig, scan,
                                      verdict, eps_forcing, eps_ttp)
    routes = build_routes(verdict, delta_E, tube_r)

    doc = dict(
        kind="n9-tube-analysis",
        generated=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        script="bounds/tube_analysis.py",
        meta=dict(
            E_star=E_star, E_star_source="thomson-workflow/data/energies.json",
            cap_certificate=dict(
                file="certificates/n9-stage-a4-typedcap-m0748_M8.json",
                certified=str(certified), certified_float=certified_f,
                cover="min inner product >= -187/250 (-0.748)",
                R1=R1, R2max=R2max, rung_source="results/typed_ladder.json"),
            layer_thickness=delta_E,
            layer_thickness_note=(
                "ΔE = E* − certified(m0748_M8)。m* = −0.7475605325955157 > −0.748 ⇒ "
                "切口含 TTP ⇒ 阶梯不收敛 E*（结构性反转保持）。薄层结论以条带片 "
                "[−1,−0.748) 盖满为前提：[−1,−0.90] 已认证（Round 2 五片全 > E*），"
                "[−0.90,−0.748) 未开始（Round 4 清单一）"),
            m_star=st["min_inner"], z_star=st["z"],
        ),
        ttp_spectrum=dict(nodes=st["nodes"], multiplicities=st["multiplicities"],
                          min_gap=st["min_gap"], half_gap=half_gap,
                          E_ttp=st["E"]),
        hessian=dict(
            tangent_dim=18, rotation_modes=3, essential_dim=15,
            spectrum18=[float(x) for x in w],
            lambda_min_quotient=lambda_min,
            rot_residual=resid_rot, rot_comp_angle=ang,
            multipliers=[float(x) for x in lam_mult],
            fd_check=[dict(fd=r["fd"], quad=r["quad"], rel=r["rel"]) for r in fd],
            note="B = Σ_{i<j}(uᵢ−uⱼ)ᵀM̃_ij(uᵢ−uⱼ) − Σᵢλᵢ(uᵢ·vᵢ)，"
                 "M̃_ij = 3r⁻⁵ddᵀ − r⁻³I（=∂²(1/r)/∂xᵢ² 块），λᵢ = ∇ᵢE·pᵢ；"
                 "切基 e1=ẑ×p/|ẑ×p|, e2=p×e1；FD=测地线二阶差分（临界点处 = Hess）"),
        ball_scan=ball,
        rigorous_lambda_min=rig,
        tube_radius=dict(
            value=tube_r,
            formula="sqrt(2·ΔE/λ_min)",
            delta_E=delta_E, lambda_min=lambda_min,
            metric=("R²⁷ 弦距离 sqrt(Σᵢ‖δᵢ‖²)，δ 为切向位移；模掉 SO(3) 旋转轨道"
                    "（3 维零模；对 TTP 轨道取 inf）与有限重标号；λ_min = 15 维"
                    "本质切空间最小特征值"),
            caveat=("二次增长展开只在 TTP 邻域成立；管内全域二次增长见 ball_scan"
                    "（数值证据，64 随机方向/半径），严格版（区间 Hessian 覆盖"
                    "27 维球邻域）未开始"),
            rigorous=(dict(radius=rig["radius"], mu0=rig["mu0"],
                           chain_best=(dict(
                               lambda_min=rig["cross_workstream"]["lambda_min_certified"],
                               radius=float(np.sqrt(
                                   2 * delta_E
                                   / rig["cross_workstream"]["lambda_min_certified"])),
                               source="full_local_min.py（独立区间链，含临界性）")
                               if "cross_workstream" in rig else None))
                      if rig else None),
        ),
        typed_slack=dict(
            identity_check=dict(
                E_minus_e_dy=E_minus_e, sum84=float(tot84), sum84_le=ok_ident,
                note="部分恒等式核对：Σ84 λ_cls(TTP) ≤ E*−e_dy（Σ_all ≥ 0）；"
                     "完整恒等式 Σ84λ+Σ_all = E−e 的随机构型机器验证在 "
                     "typed_ladder --selftest（已过）"),
            eps_forcing=eps_forcing,
            eps_forcing_derivation=(
                "λ_cls ≤ (E*−e_dy) + Σ_{cls'≠cls} R1_orbit' ≤ (E*−e_dy) + "
                "Σ_counts·R1；数值 = 4.144e-4 + 8.7e-7；minorant 侧 (1+R2) 因子"
                "≤1.5e-9 相对修正，忽略级"),
            eps_ttp_level=eps_ttp,
            per_orbit={o: dict(n=len(per_orbit[o]["values"]),
                               max=max(per_orbit[o]["values"]),
                               min=min(per_orbit[o]["values"]),
                               mean=float(np.mean(per_orbit[o]["values"])))
                       for o in ORBITS},
            local_model=local_model,
            structure_change=("untyped→typed：504→84 项、10→3 轨道；单项放大 "
                              "×504型→×1（每类独立 ≤ ε_forcing）；这是 Round 2 "
                              "诊断（untyped 时代）后需要重估的几何变化"),
        ),
        spectral_tube=scan,
        verdict=verdict,
        lemma_design=lemma_design,
        routes=routes,
        provenance=dict(
            runtime_s=round(time.time() - t0, 1),
            commands=[f"python3 numerics/bounds/tube_analysis.py --n-grid {args.n_grid}"],
            inputs=[str(CERT.relative_to(REPO)), str(LADDER_RESULTS.relative_to(REPO)),
                    str(LOCAL_MIN.relative_to(REPO)),
                    "thomson-workflow/data/energies.json"],
        ),
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(doc, f, indent=1, ensure_ascii=False)
    log(f"[out  ] {args.out} 写出（{time.time() - t0:.0f}s）")


def build_lemma_design(delta_E, lambda_min, tube_r, rig, scan, verdict,
                       eps_forcing, eps_ttp):
    """引理链（管半径→刚性→局部极小→排除）逐成分状态。"""
    rho = verdict.get("rho_spec_at_forcing")
    return [
        dict(component="L0 条带片 [−1,−0.748) 全部 > E*（不含 TTP）",
             status="部分已严格",
             quant="[−1,−0.90] 5 片已认证（Round 2 slab_band，certified "
                   "25.7697–25.8159 全 > E*）；[−0.90,−0.748) 未开始（Round 4 "
                   "清单一：typed (8,6) SDPA-GMP 条带；①段 [−0.90,−0.845] 实测"
                   "正裕度 +0.9e-3~+6.1e-3，②段 [−0.845,−0.755] 须逐片实测）"),
        dict(component="L1 cap：m ≥ −0.748 ⇒ E ≥ 25.759571186（薄层下界）",
             status="已严格",
             quant=f"certificates/n9-stage-a4-typedcap-m0748_M8.json（38 PSD 块"
                   f"精确 LDLᵀ 全过、--verify-cert 进程外复核）；E*−c = "
                   f"{delta_E:.4e}"),
        dict(component="L2 强制：E ≤ E* ⇒ 每类 λ_cls ≤ ε_forcing ≈ 4.15e-4",
             status="证书数据已严格；本轮把 ε_forcing 落到逐类口径（数值推导，"
                    "公式精确）",
             quant=f"恒等式 Σ84λ+Σ_all = E−e（typed_ladder 精确自检）+ λ ≥ −R1；"
                   f"ε_forcing = {eps_forcing:.4e}；typed 放大 ×1/类（untyped "
                   f"是 ×504 型）"),
        dict(component="L3 谱管：λ_orbit ≤ ε ⇒ 各内积距 6 节点 ≤ ρ_spec(ε)",
             status="数值证据（本轮 3 轨道网格扫描重估）——结论为结构性不足",
             quant=(f"ρ_spec(ε_forcing) = {verdict.get('rho_spec_at_forcing'):.4f}"
                    f"（差 {verdict.get('ratio_at_forcing'):.0f} 倍）；压到零集地板 "
                    f"ε=1.5e-8 仍 {verdict.get('rho_spec_at_floor'):.4f}"
                    f"（差 {verdict.get('ratio_at_floor'):.1f} 倍）——零集含伪近零 "
                    "(0.1961,0.1961,0.1961)（三轨道共同最深点 9.4e-9）与 AAB/ABC "
                    "远端 3.7e-6 级近零；逐三元组松弛下 L3 在本证书族内不可能达标 "
                    "⇒ 走路线 b（tube certificate）或 d_H=16/(9,6)"
                    if verdict.get("rho_spec_at_floor") else "扫描未跑")),
        dict(component="L4 组合刚性：内积 ∈ 6 节点 0.0185-管 ⇒ 邻型唯一 = TTP",
             status="未开始（前置 = L3 达标）",
             quant="形态：strategy.md §0.4 邻型计数；TTP 重数 6/6/3/3/6/12 与"
                   "幂和矩条件（i≤3，随 H 次数可到 i≤5）"),
        dict(component="L5 Gram→构型：‖G−G_TTP‖∞ ≤ η ⇒ 弦距离 ≤ C√η 型（Procrustes）",
             status="标准不等式（引用未写证明）+ 数值常数可算，未开始",
             quant="PSD Procrustes：dist²_F(X, TTP·O) ≤ ‖ΔG‖_F·2/(σ_min+…) 型；"
                   "常数依赖 G_TTP 谱（可数值算出）"),
        dict(component="L6 局部极小/二次增长：管内 E ≥ E* + ½λ‖δ‖²",
             status="TTP 点处已严格（两条独立区间链：本文件 μ₀ + full_local_min"
                    " 0.14378982 含临界性）；管内全域（Taylor 三阶余项/球邻域）"
                    "未开始",
             quant=f"λ_min = {lambda_min:.6f}（数值，FD 复核"
                   + (f"，本文件区间 μ₀ = {rig['mu0']:.6f}" if rig else "")
                   + (("，full_local_min 区间 ≥ %.8f（链上取强，r=%.5f）"
                       % (rig["cross_workstream"]["lambda_min_certified"],
                          float(np.sqrt(2 * delta_E / rig["cross_workstream"][
                              "lambda_min_certified"]))))
                      if rig and "cross_workstream" in rig else "")
                   + f"）；r_tube = {tube_r:.4f}；ball_scan 为管内证据"),
        dict(component="L7 排除/拼接：L0∪L1∪(L2→L3→L4→L5→L6) ⇒ 全空间 E ≥ E*",
             status="未开始", quant="书面拼接产物（Round 2 起遗留）"),
    ]


def build_routes(verdict, delta_E, tube_r):
    """全局排除的三条候选路线与取舍。"""
    rho0 = verdict.get("rho_spec_at_floor")
    ratio0 = verdict.get("ratio_at_floor")
    ratiof = verdict.get("ratio_at_forcing")
    out = dict(
        a_cap_thinning=dict(
            idea="追加 a₀=−0.7476 的 (8,6) typed cap 解（m* 下方 3.95e-5，区域更小）"
                 "压薄层厚度 ΔE",
            estimate=("ΔE 4.153e-4 → 预计 ~3.5–3.9e-4：(7,6) 阶梯 −0.755→−0.748 每降 "
                      "5e-3 切口 e 升 ~6e-5；(8,6) 在 −0.748 原始间隙已 4.14e-4，"
                      "切口再降 4e-5 的预期收益 ≤1e-4 级（外推判断，无已解数据）"),
            effect=(f"r_tube ∝ √ΔE：−(3~8)%（0.0760 → ~0.072–0.074）。但 L3 谱管："
                    f"本轮实测 ρ_spec 在 ε=4.15e-4 为 {verdict.get('rho_spec_at_forcing'):.4f}、"
                    f"压到零集地板 1.5e-8（>4 个数量级）仍 {rho0:.4f}（差 {ratio0:.0f} 倍）"
                    if rho0 else "待扫描数据"),
            cost="SDPA-GMP 单档 ~3.3h（m0748_M8 实测 11792.6s）+ 认证",
            verdict=(f"不动用（本轮判定）：谱管瓶颈在 slack 零集几何不在厚度——"
                     f"ε 全幅压缩 4 个数量级 ρ_spec 只从 {verdict.get('rho_spec_at_forcing'):.3f}"
                     f"→ {rho0:.3f}，仍差 {ratio0:.0f} 倍；a₀=−0.7476 的预期厚度收益"
                     f"(≤1e-4) 对 L3 无实质影响（对 L1 拼合界也只抬 ~1e-4 级）"
                     if rho0 else "待数据"),
        ),
        b_tube_certificate=dict(
            idea="以'距 TTP 谱距离'为条件的专项证书（tube certificate）：两点 minorant "
                 "从全局单区间改为 6 节点管外 6 片分段（每片独立 Lukács/SOS 乘子，"
                 "管半径 ρ 为参数）⇒ 证'某内积距全部节点 ≥ ρ ⇒ E ≥ E*(ρ)'；配合 L2 "
                 "强制得 ρ_spec ≤ ρ(ε) 可调",
            design="h_AA/h_AB 分段化：对每片 [ν_k+ρ, ν_{k+1}−ρ] 加区间 SOS 乘子"
                   "（slab_band 的一侧区间机制已有）；三点 slack 域乘子族同步加 "
                   "(t−ν_k)²−ρ² 型因子；SDP 规模 = 现 cap + 6×2 片乘子块，复用 "
                   "typed_ladder 管线（SDPA-GMP 导出 + dyadic 认证不变）",
            cost="单档规模与 m0748_M8 同量级（~3h/档）；ρ 扫描 2-3 档",
            risk=("本轮证据指出的核心风险：typed 证书的 slack 在远离 TTP 模式处有 "
                  "3.7e-6 级近零（AAB/ABC worst 点），管外分段乘子必须把这些区域"
                  "'烧掉'——可行性未验证，列为下一轮首选实验；若管边极点处 minorant "
                  "仍贴不住，则须 d_H=16/(9,6) 或 N=7 式精确取等"),
        ),
        c_literature=dict(
            idea="已知球面码/能量定量稳定性结果移植",
            assessment="无可直接移植的定量结果：N=9 TTP 非普适最优（不在 "
                       "Cohn–Kumar 表），能量稳定性无现成率；最近模板是 KLT N=7 "
                       "的管+刚性收尾本身（即路线 b 的机制来源）；定性紧性论证"
                       "（严格局部极小 ⇒ 某半径内唯一）无显式常数，对 4e-4 级"
                       "间隙无用",
        ),
    )
    return out


if __name__ == "__main__":
    main()
