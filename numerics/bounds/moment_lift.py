#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""moment_lift.py — R7-1 矩容器抬天花板：KLT 引理 4.2 矩容器族 M_k(Y) ≽ 0 接入
typed (3,3,3) S₃ 商三点恒等式（D7-hermite 指定的 campaign 第 2 轮首选实验）.

## 数学（references/klt-n8-paper.pdf p12–13，本会话 pypdf 提取）

KLT 记 Q₀=1, Q₁=t−uv, Q_k=2(t−uv)Q_{k−1}−(1−u²)(1−v²)Q_{k−2}；
(S_k)_{ab}=Sym(u^a v^b Q_k)（Sym=六置换平均），M_k(Y)=Σ_{i,j,l 含重复}S_k(内积三元组)。

**引理 4.2（M_k(Y) ≽ 0，N 无关）**：固定基点 x，取 x^⊥ 的正交基 e₁,e₂，
ζ_y=e₁·y+i·e₂·y ⟹ Re(ζ_y ζ̄_z)=t−uv、|ζ_y ζ̄_z|²=(1−u²)(1−v²) ⟹
Q_k=Re(ζ_y^k)Re(ζ_z^k)+Im(ζ_y^k)Im(ζ_z^k)，未对称化和=两个外积和 ≽ 0；
对基点求和即得（对称化经指标重标号不变）。

**N=9 的 R_k 修正（本文件推导；KLT 原式 R_k=6S_k+ΣS_k(·,·,1)+δ_{k0}J/7 是 N=8 专用）**：
M_k = T_k + 3D_k + 9δ_{k0}J（T_k=不同下标和、D_k=有序对不同 S_k(·,·,1)、
全等 (i,i,i) 贡献 S_k(1,1,1)=δ_{k0}J，N=9）。要求 Ψ_Y R_k = 6M_k（Ψ=不同下标
有序三元组和）⟹ 6T_k + β·3·7·D_k + γ·504·J = 6T_k + 18D_k + 54J ⟹
**β = 6/7、γ = 6/56 = 3/28**。N=8 时 β=1、γ=1/7 复原 KLT 原式。

**接入三点恒等式（结构保留，新增 Σ⟨F_k,M_k⟩ 项）**：在 hermite_ladder 的
精确恒等式 Σ_{i<j}h−e = Σ_T λ_T + Σ_all s（typed_ladder 组合恒等式，h 固定
Hermite minorant）上加容器族 G_k ≽ 0：

    (∗)  Σ_{i<j}h − e = Σ_T [λ_T − Σ_k⟨G_k,R_k⟩] + Σ_all s + Σ_k⟨G_k,M_k(Y)⟩

（Σ_T 对无序不同下标三元组；Σ_all 对全部有序三元组含重复）。因 R_k 全对称，
Σ_T⟨G,R⟩ = ⟨G, ΨR/6⟩ = ⟨G,M_k⟩，恒等式精确成立（自检）。界链：
λ′=λ−Σ⟨G,R⟩ = SOS ⟹ 逐三元组 λ′ ≥ −R1；Σ_all ≥ 0（typed 引理 4.1，F ⪰ 0）；
Σ⟨G,M_k⟩ ≥ 0（引理 4.2）⟹ certified = e − (3R1_A+54R1_B+27R1_C)（归一化
3c_A+54c_B+27c_C−e−9ΣF₀=0 结构不变，容器不入归一化）。新自由度的语义：
λ_T 逐点非负要求放松为「三元组和 + 全局矩容器补偿 ≥ 0」——⟨G,R⟩(u,v,t)
可逐点为负（如 Sym(u) 于 (−1,−1,−1)），这正是 λ-SOS 天花板之上的新锥。

用法（thomson-n9 下；探针用 numerics/.venv 解释器（cvxpy+Clarabel））：
  numerics/.venv/bin/python numerics/bounds/moment_lift.py --selftest     # 精确恒等式＋引理 4.2 抽查
  numerics/.venv/bin/python numerics/bounds/moment_lift.py --probe        # 相位 A 判死活探针
  numerics/.venv/bin/python numerics/bounds/moment_lift.py --spot         # ≥200 构型 M_k≽0＋负对照（写 JSON 段）
  python3 numerics/bounds/moment_lift.py --cap -0.748 --M 8              # 相位 B（SDPA-GMP）
  python3 numerics/bounds/moment_lift.py --verify-cert certificates/n9-stage-a6-momentcap-m0748_M8.json

R8-2 锚定精确取等探针（SDPA-GMP 精确行版；D19 裁决 3）：
  python3 numerics/bounds/moment_lift.py --anchor-check                  # 锚定导出行泛函自检（快速）
  python3 numerics/bounds/moment_lift.py --anchor-cap A                  # Arm A：(7,6) 全组+容器
  python3 numerics/bounds/moment_lift.py --anchor-cap B                  # Arm B：(9,6) 全组+容器
  python3 numerics/bounds/moment_lift.py --anchor-cap C                  # Arm C：(9,6) 无容器（诊断）
  python3 numerics/bounds/moment_lift.py --anchor-finalize               # 幂等重算＋写 anchor_probe_m9.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import random
import subprocess
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
WORKFLOW_CERTS = HERE.parents[2] / "thomson-workflow" / "certificates"
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "typed"))
sys.path.insert(0, str(WORKFLOW_CERTS))

from typed_ladder import (QuotientMaps, FRing, frac_dec, parse_result,   # noqa: E402
                          rung_tag, load_E_star, code_version,
                          F0, F1, fail, CertError)
from hermite_ladder import (fixed_minorant, pad_h, HermiteCapExporter,    # noqa: E402
                            SEED as SEED_HERMITE, E_TTP_TUBE)
from hermite_ladder import (solution_from_parse_cap as _hl_sol_from_parse,
                            raw_residuals_cap as _hl_raw_resid,
                            STALLED_R1_TOL)
from sdp_certify import dyad, repair_psd                                  # noqa: E402
from hermite_minorant import (hermite_minorant_dyadic,                   # noqa: E402
                              load_ttp_spectrum)
from thomson_certs.exact import is_positive_definite                      # noqa: E402

SEED = 20261007
N = 9
PHI_TOL = Fraction(1, 10 ** 6)
OLD_CAP_BEST = Fraction("25.759571185601")     # typed m0748_M8（D10 cap 记账值，新证书须严格超越才 full）
E_HP = Fraction("25.75998653127")              # highPrecision 口径（D2）
Z_STAR_INTERVAL = (0.703648376463, 0.703649139406)   # full_local_min zStarInterval（锚定对照层）
PARAM_SDPA_TUNED = """2000unsigned int maxIteration;
1.0E-25\tdouble 0.0 < epsilonStar;
1.0E4   double 0.0 < lambdaStar;
2.0   \tdouble 1.0 < omegaStar;
-1.0E5  double lowerBound;
1.0E5   double upperBound;
0.05   \tdouble 0.0 <= betaStar <  1.0;
0.15   \tdouble 0.0 <= betaBar  <  1.0, betaStar <= betaBar;
0.9    \tdouble 0.0 < gammaStar <  1.0;
1.0E-25\tdouble 0.0 < epsilonDash;
200     precision
"""


# ============================================================ 矩容器映射（精确）
def minorant_for(M: int, k: int = 48) -> dict:
    """d_H 尺寸感知的固定 Hermite minorant。

    6 节点（值＋导）minorant 为 deg 11 ⟹ 需 d_H ≥ 11（M ≥ 6.5 即 M ≥ 7）。
    d_H 不足时取最大可容纳节点数（去最大节点，保留低端节点——cap 域 t ≥ −0.748
    的困难区在低端）；余项公式 φ^{(2n)}(ξ)/(2n)!·∏(t−ν_k)² ≥ 0 对任意节点集
    全局成立（φ 各阶导 > 0），φ ≥ M 证书链不变。M ≥ 7 时与 a5 引擎
    fixed_minorant(k) 完全一致（探针/认证同一条链）。"""
    d_H = 2 * M - 2
    n_nodes = min(6, (d_H + 1) // 2)
    if n_nodes >= 6:
        return fixed_minorant(k)
    spec = load_ttp_spectrum()
    return hermite_minorant_dyadic(spec["nodes"][:n_nodes], k=k)


def sym6(ring: FRing, vec):
    """六置换平均 Sym（KLT §4.2）；perm_maps[0..5] 恰为 (u,v,t) 的全部置换。"""
    out = [F0] * ring.nmon
    for which in range(6):
        pv = ring.perm(vec, which)
        out = [x + y for x, y in zip(out, pv)]
    return [x / 6 for x in out]


def subst3(ring: FRing, vec, img_u, img_v, img_t):
    """变量替换 p(u,v,t) → p(img_u, img_v, img_t)（img 为 Poly3 向量）。"""
    out = ring.zero()
    for p, c in enumerate(vec):
        if c == 0:
            continue
        i, j, l = ring.mons[p]
        f = ring.mono((0, 0, 0), c)
        for (img, deg) in ((img_u, i), (img_v, j), (img_t, l)):
            for _ in range(deg):
                f = ring.mul(f, img)
        out = [x + y for x, y in zip(out, f)]
    return out


class MomentMaps:
    """S₃ 商 N=9 矩容器族：S_k[a][b]=Sym(u^a v^b Q_k)、R_k（N=9 常数 6/7、3/28）。

    sizes[k] = M−k（与 QuotientMaps.F_sizes 同形）；R_k 全 (u,v,t) 对称且 (a,b)
    对称（断言）。R_k 的常数修正项 δ_{k0}·(3/28)·J 由构造后置。
    """

    def __init__(self, qm: QuotientMaps, beta=Fraction(6, 7), gamma=Fraction(3, 28),
                 label="N9"):
        self.qm, self.ring = qm, qm.ring
        self.beta, self.gamma, self.label = beta, gamma, label
        self.K = qm.K
        self.sizes = list(qm.F_sizes)
        self.S, self.R = [], []
        u_vec = qm.ring.mono((1, 0, 0))
        v_vec = qm.ring.mono((0, 1, 0))
        t_vec = qm.ring.mono((0, 0, 1))
        one = qm.ring.mono((0, 0, 0))
        for k in range(self.K):
            mk = self.sizes[k]
            S_k = [[None] * mk for _ in range(mk)]
            for a in range(mk):
                for b in range(mk):
                    Y = qm.Y_cols[qm.Y_index[(k, a, b)]]
                    S_k[a][b] = sym6(qm.ring, Y)
            for a in range(mk):
                for b in range(mk):
                    assert S_k[a][b] == S_k[b][a], f"S_{k}[{a}][{b}] 不对称"
            R_k = [[None] * mk for _ in range(mk)]
            for a in range(mk):
                for b in range(mk):
                    S = S_k[a][b]
                    sub_uu = subst3(qm.ring, S, u_vec, u_vec, one)
                    sub_vv = subst3(qm.ring, S, v_vec, v_vec, one)
                    sub_tt = subst3(qm.ring, S, t_vec, t_vec, one)
                    acc = [6 * x for x in S]
                    for sub in (sub_uu, sub_vv, sub_tt):
                        acc = [x + beta * y for x, y in zip(acc, sub)]
                    R_k[a][b] = acc
            if k == 0:
                const = qm.ring.index[(0, 0, 0)]
                for a in range(mk):
                    for b in range(mk):
                        R_k[a][b][const] += gamma
            for a in range(mk):
                for b in range(mk):
                    assert R_k[a][b] == R_k[b][a], f"R_{k}[{a}][{b}] 不对称"
            self.S.append(S_k)
            self.R.append(R_k)

    def container_vec(self, data: dict):
        """Σ_k⟨G_k,R_k⟩ 的 Poly3 系数向量（G=data['G'] 对称）。"""
        ring = self.ring
        out = ring.zero()
        for k in range(self.K):
            Gk = data["G"][k]
            mk = self.sizes[k]
            for a in range(mk):
                for b in range(mk):
                    g = Gk[a][b]
                    if g:
                        out = [x + g * y for x, y in zip(out, self.R[k][a][b])]
        return out


def moment_lam(qm: QuotientMaps, mm: MomentMaps, orbit: str, data: dict):
    """λ′_orbit = qm.lam(orbit, data) − Σ_k⟨G_k,R_k⟩（R 全对称 ⟹ 轨道无关减项）。"""
    base = qm.lam(orbit, data)
    cv = mm.container_vec(data)
    return [x - y for x, y in zip(base, cv)]


def moment_full_lam(qm: QuotientMaps, mm: MomentMaps, cls, data: dict):
    base = qm.full_lam(cls, data)
    cv = mm.container_vec(data)
    return [x - y for x, y in zip(base, cv)]


# ============================================================ 精确配置求值
def qpow_scalar(u, v, t, K):
    """标量 Q_k 递推（exact Fraction）：返回 [Q_0..Q_{K−1}] 于 (u,v,t)。"""
    out = [F1]
    if K > 1:
        out.append(t - u * v)
    tm = t - u * v
    om = (1 - u * u) * (1 - v * v)
    while len(out) < K:
        out.append(2 * tm * out[-1] - om * out[-2])
    return out


def M_kernel_exact(qm: QuotientMaps, Gram):
    """M_k(Y)（引理 4.2 对象）的**核和**口径：M_k[a][b]=Σ_{有序含重复} g_ij^a g_il^b Q_k。
    与 S_k 口径相等（对称化重标号），由 selftest 在随机配置上精确核对。"""
    Ms = [[[F0] * mk for _ in range(mk)] for mk in qm.F_sizes]
    pmax = qm.M  # 幂表最高次 = M−1
    pw = [[[F1] * pmax for _ in range(N)] for _ in range(N)]
    for i in range(N):
        for j in range(N):
            g = Gram[i][j]
            for a in range(1, pmax):
                pw[i][j][a] = pw[i][j][a - 1] * g
    for i in range(N):
        for j in range(N):
            for l in range(N):
                u, v, t = Gram[i][j], Gram[i][l], Gram[j][l]
                Qs = qpow_scalar(u, v, t, qm.K)
                for k in range(qm.K):
                    Q = Qs[k]
                    mk = qm.F_sizes[k]
                    Mk = Ms[k]
                    pi = pw[i][j]
                    pl = pw[i][l]
                    for a in range(mk):
                        pa = pi[a]
                        row = Mk[a]
                        for b in range(mk):
                            row[b] += pa * pl[b] * Q
    return Ms


def M_Sroute_exact(qm: QuotientMaps, mm: MomentMaps, Gram):
    """M_k(Y) 的 S_k 多项式口径（慢；selftest 用）：Σ S_k[a][b](三元组)。"""
    ring = qm.ring
    Ms = [[[F0] * mk for _ in range(mk)] for mk in qm.F_sizes]
    for k in range(qm.K):
        mk = qm.F_sizes[k]
        for a in range(mk):
            for b in range(mk):
                acc = F0
                for i in range(N):
                    for j in range(N):
                        for l in range(N):
                            acc += ring.eval3(mm.S[k][a][b],
                                              Gram[i][j], Gram[i][l], Gram[j][l])
                Ms[k][a][b] = acc
    return Ms


def PsiR_exact(qm: QuotientMaps, mm: MomentMaps, Gram):
    """Ψ_Y R_k（不同下标有序三元组和），矩阵口径；selftest 断言 == 6·M_k。"""
    ring = qm.ring
    out = [[[F0] * mk for _ in range(mk)] for mk in qm.F_sizes]
    for k in range(qm.K):
        mk = qm.F_sizes[k]
        for a in range(mk):
            for b in range(mk):
                acc = F0
                for i in range(N):
                    for j in range(N):
                        if j == i:
                            continue
                        for l in range(N):
                            if l == i or l == j:
                                continue
                            acc += ring.eval3(mm.R[k][a][b],
                                              Gram[i][j], Gram[i][l], Gram[j][l])
                out[k][a][b] = acc
    return out


def zeta_M_float(qm: QuotientMaps, X):
    """引理 4.2 ζ 外积和口径（float64 数值见证）：M_k = Σ_x [r rᵀ + q qᵀ]。"""
    import numpy as np
    Ms = [np.zeros((mk, mk)) for mk in qm.F_sizes]
    Gm = X @ X.T
    for i in range(N):
        x = X[i]
        e1 = np.array([1.0, 0, 0]) if abs(x[0]) < 0.9 else np.array([0, 1.0, 0])
        e1 = e1 - x * (e1 @ x)
        e1 /= np.linalg.norm(e1)
        e2 = np.cross(x, e1)
        zeta = X @ e1 + 1j * (X @ e2)
        g = Gm[i]
        for k in range(qm.K):
            zk = zeta ** k if k > 0 else np.ones(N, dtype=complex)
            for a in range(qm.F_sizes[k]):
                ra = (g ** a * zk.real).sum()
                qa = (g ** a * zk.imag).sum()
                for b in range(qm.F_sizes[k]):
                    rb = (g ** b * zk.real).sum()
                    qb = (g ** b * zk.imag).sum()
                    Ms[k][a][b] += ra * rb + qa * qb
    return Ms


# ============================================================ 精确自检
def random_config_exact(rng, bits=6):
    from typed_ladder import random_rational_config
    return random_rational_config(rng, N)


def random_data_with_G(qm: QuotientMaps, rng, scale_bits=10):
    """随机 ψ/c/e + PSD F + PSD G（c_C 由归一化精确重算）。"""
    d_H = qm.d_H
    data = dict(
        psi_AA=[Fraction(rng.randint(-1 << scale_bits, 1 << scale_bits), 1 << scale_bits)
                for _ in range(d_H + 1)],
        psi_AB=[Fraction(rng.randint(-1 << scale_bits, 1 << scale_bits), 1 << scale_bits)
                for _ in range(d_H + 1)],
        e=Fraction(rng.randint(20 << 8, 30 << 8), 1 << 8),
        c_A=Fraction(rng.randint(-8, 8), 4),
        c_B=Fraction(rng.randint(-8, 8), 4),
        F=[], G=[])
    for name in ("F", "G"):
        for mk in qm.F_sizes:
            Gm = [[Fraction(rng.randint(-8, 8), 4) for _ in range(mk)] for _ in range(mk)]
            data[name].append([[sum(Gm[i][t] * Gm[j][t] for t in range(mk)) for j in range(mk)]
                               for i in range(mk)])
    s111 = sum(sum(row) for row in data["F"][0])
    data["c_C"] = (data["e"] + qm.s111_factor * s111
                   - qm.nrm["c_A"] * data["c_A"] - qm.nrm["c_B"] * data["c_B"]) / qm.nrm["c_C"]
    return data


def identity_moment_selftest(qm: QuotientMaps, mm: MomentMaps, rng, trials=2):
    """(∗) 修正三点恒等式：Σh−e = Σ_T λ′_T + Σ_all s + Σ⟨G,M_k⟩（精确 ==0）。"""
    ring = qm.ring
    dy = minorant_for(qm.M)
    h_AA = pad_h(dy["coeffs"], qm.d_H)
    types = [0] * 3 + [1] * 3 + [2] * 3
    for _ in range(trials):
        data = random_data_with_G(qm, rng)
        data["h_AA"] = list(h_AA)
        data["h_AB"] = list(h_AA)
        X = random_config_exact(rng)
        Gram = [[sum(a * b for a, b in zip(xi, xj)) for xj in X] for xi in X]
        s_vec, _ = qm.s_forms(data)
        sum_all = F0
        for i in range(N):
            for j in range(N):
                for l in range(N):
                    sum_all += ring.eval3(s_vec, Gram[i][j], Gram[i][l], Gram[j][l])
        sum_lam = F0
        lam_by_cls = {cls: moment_full_lam(qm, mm, cls, data)
                      for (cls, _o, _p) in qm.full_classes}
        for (i, j, l) in combinations(range(N), 3):
            tt = sorted([(types[i], i), (types[j], j), (types[l], l)])
            (_r0, i0), (_r1, j0), (_r2, l0) = tt
            cls = tuple(x[0] for x in tt)
            sum_lam += ring.eval3(lam_by_cls[cls], Gram[i0][j0], Gram[i0][l0], Gram[j0][l0])
        Ms = M_kernel_exact(qm, Gram)
        sum_container = F0
        for k in range(qm.K):
            Gk, Mk = data["G"][k], Ms[k]
            mk = qm.F_sizes[k]
            for a in range(mk):
                for b in range(mk):
                    if Gk[a][b]:
                        sum_container += Gk[a][b] * Mk[a][b]
        sum_H = F0
        for i in range(N):
            for j in range(i + 1, N):
                key = qm.h_of["AA" if types[i] == types[j] else "AB"]
                sum_H += ring.eval1(data[key], Gram[i][j])
        lhs, rhs = sum_lam + sum_all + sum_container, sum_H - data["e"]
        assert lhs == rhs, f"(∗) 恒等式失败：{lhs} != {rhs}"
    return dict(ok=True, trials=trials)


def psiR_selftest(qm: QuotientMaps, mm: MomentMaps, Gram):
    """Ψ_Y R_k == 6·M_k（矩阵逐元素，exact）。"""
    PR = PsiR_exact(qm, mm, Gram)
    Ms = M_kernel_exact(qm, Gram)
    for k in range(qm.K):
        mk = qm.F_sizes[k]
        for a in range(mk):
            for b in range(mk):
                assert PR[k][a][b] == 6 * Ms[k][a][b], \
                    f"ΨR ≠ 6M：k={k} ({a},{b}) {PR[k][a][b]} vs {6*Ms[k][a][b]}"
    return True


def container_validity_selftest(M: int, K: int, lo: Fraction, n_psd_configs: int,
                                rng, n_identity: int = 2):
    """容器族有效性全套：
    (1) S 口径 M_k == 核和口径 M_k（3 配置，exact）；
    (2) 核和 M_k == ζ 外积和 M_k（3 配置，float 相对误差 <1e-9）；
    (3) ≥n_psd_configs 随机配置核和 M_k ≽ 0（exact LDLᵀ 正定）；
    (4) ΨR == 6M（2 配置）＋(∗) 恒等式（n_identity 配置）。"""
    import numpy as np
    qm = QuotientMaps(lo, M, K)
    mm = MomentMaps(qm)
    t0 = time.time()
    # (1) S 口径 == 核和口径（3 配置）
    for _ in range(3):
        X = random_config_exact(rng)
        Gram = [[sum(a * b for a, b in zip(xi, xj)) for xj in X] for xi in X]
        Ma, Mb = M_Sroute_exact(qm, mm, Gram), M_kernel_exact(qm, Gram)
        for k in range(K):
            assert Ma[k] == Mb[k], f"S 口径 ≠ 核和口径：k={k}"
    ok1 = dict(ok=True, configs=3)
    # (2) ζ 外积和（float 见证，3 配置）：与核和口径相对误差 < 1e-9
    worst = 0.0
    for _ in range(3):
        from sdp_certify import rational_point
        Xr = [rational_point(Fraction(rng.randint(-64, 64), 64),
                             Fraction(rng.randint(-64, 64), 64)) for _ in range(N)]
        Gramr = [[sum(a * b for a, b in zip(xi, xj)) for xj in Xr] for xi in Xr]
        Mk_ = M_kernel_exact(qm, Gramr)
        Mz = zeta_M_float(qm, np.array([[float(c) for c in row] for row in Xr]))
        for k in range(K):
            scale = max(abs(float(x)) for row in Mk_[k] for x in row)
            err = max(abs(float(Mk_[k][a][b]) - Mz[k][a][b])
                      for a in range(qm.F_sizes[k]) for b in range(qm.F_sizes[k]))
            worst = max(worst, err / max(scale, 1e-300))
    assert worst < 1e-9, f"ζ 外积和与核和口径相对误差 {worst:.2e} 超阈"
    ok2 = dict(ok=True, configs=3, worst_rel_err=worst)
    # (3) ≥n_psd_configs 随机配置：核和 M_k ≽ 0（exact LDLᵀ）
    n_ok = 0
    min_diag_frac = None
    for _ in range(n_psd_configs):
        X = random_config_exact(rng)
        Gram = [[sum(a * b for a, b in zip(xi, xj)) for xj in X] for xi in X]
        Ms = M_kernel_exact(qm, Gram)
        for k in range(K):
            if not is_positive_definite(Ms[k]):
                # 严格 LDLᵀ 失败可能是奇异（测度零事件）——float 判奇异与否，如实区分
                import numpy as _np
                fM = _np.array([[float(x) for x in row] for row in Ms[k]])
                eig = _np.linalg.eigvalsh(fM)
                raise AssertionError(
                    f"M_{k} ≽0 失败（LDLᵀ 拒绝；float eig {eig.min():.3e}）")
            d0 = Ms[k][0][0]
            min_diag_frac = d0 if min_diag_frac is None else min(min_diag_frac, d0)
        n_ok += 1
    ok3 = dict(ok=True, configs=n_ok, blocks=K, min_m00=str(min_diag_frac))
    # (4) ΨR == 6M（2 配置）＋ (∗)
    for _ in range(2):
        X = random_config_exact(rng)
        Gram = [[sum(a * b for a, b in zip(xi, xj)) for xj in X] for xi in X]
        psiR_selftest(qm, mm, Gram)
    ok4 = psiR_selftest.__name__ + ":ok"
    ok5 = identity_moment_selftest(qm, mm, rng, trials=n_identity)
    return dict(M=M, K=K, nmon=qm.nmon, S_vs_kernel=ok1, zeta_vs_kernel=ok2,
                psd_spot=ok3, psiR="ok(configs=2)", identity=ok5,
                wall_s=round(time.time() - t0, 1))


def negative_controls(M: int, K: int, lo: Fraction, rng):
    """负对照三件（全部必须被检出）：
    (a) 篡改容器块＝N=8 常数（β=1、γ=1/7）⟹ ΨR == 6M 必败；
    (b) 篡改 S_k 一个系数位（2^-10）⟹ S 口径 == 核和口径必败；
    (c) 随机对称（非 PSD）G 块 ⟹ LDLᵀ PSD 检查必拒且 Σ⟨G,M_k⟩ 可为负。"""
    qm = QuotientMaps(lo, M, K)
    mm = MomentMaps(qm)
    # (a) N=8 常数
    mm8 = MomentMaps(qm, beta=F1, gamma=Fraction(1, 7), label="N8-wrong")
    X = random_config_exact(rng)
    Gram = [[sum(a * b for a, b in zip(xi, xj)) for xj in X] for xi in X]
    PR = PsiR_exact(qm, mm8, Gram)
    Ms = M_kernel_exact(qm, Gram)
    ok_a = any(PR[k][a][b] != 6 * Ms[k][a][b]
               for k in range(K) for a in range(qm.F_sizes[k])
               for b in range(qm.F_sizes[k]))
    assert ok_a, "负对照 (a) 未触发：N=8 常数未被检出"
    # (b) 篡改 S_k 系数
    import copy
    mm2 = MomentMaps(qm)
    mm2.S[0][0][0][qm.ring.index[(0, 0, 0)]] += Fraction(1, 1 << 10)
    Ma, Mb = M_Sroute_exact(qm, mm2, Gram), Ms
    ok_b = any(Ma[k][a][b] != Mb[k][a][b] for k in range(K)
               for a in range(qm.F_sizes[k]) for b in range(qm.F_sizes[k]))
    assert ok_b, "负对照 (b) 未触发：篡改 S_k 未被检出"
    # (c) 随机对称非 PSD G
    bad_psd_detected = False
    neg_sum_found = False
    for _ in range(200):
        mk = qm.F_sizes[0]
        Gb = [[Fraction(rng.randint(-4, 4)) for _ in range(mk)] for _ in range(mk)]
        Gb = [[Gb[i][j] + Gb[j][i] for j in range(mk)] for i in range(mk)]  # 对称
        Gb[0][0] = -abs(Gb[0][0]) - 1                                       # 保证负对角
        if not is_positive_definite(Gb):
            bad_psd_detected = True
        val = sum(Gb[a][b] * Ms[0][a][b] for a in range(mk) for b in range(mk))
        if val < 0:
            neg_sum_found = True
        if bad_psd_detected and neg_sum_found:
            break
    assert bad_psd_detected, "负对照 (c) 未触发：非 PSD 块未被 LDLᵀ 检出"
    assert neg_sum_found, "负对照 (c) 未触发：Σ⟨G,M⟩ 未出现负值"
    return dict(a_n8_constants_detected=True, b_tampered_S_detected=True,
                c_nonpsd_G_detected=True, c_negative_container_sum_found=True)


# ============================================================ float 探针（cvxpy）
def build_cap_maps(qm: QuotientMaps, mm: MomentMaps, h_AA, h_AB):
    """cap SDP 的精确约束映射（Fraction 主本；float 副本供 cvxpy）。

    布局：标量 [e, ψ_AA×(d_H+1), ψ_AB×(d_H+1), c_A, c_B, c_C]，F 块（逐块 mk² 列，
    行主序 a·mk+b，含全部有序 (a,b) 列），G 块同构，SOS 块（逐轨道逐名）。
    行约束：h_const + 标量 + F − G − SOS == 0（即 λ − Σ⟨G,R⟩ − SOS == 0）。"""
    ring = qm.ring
    d_H1 = qm.d_H + 1
    lay = {"e": 0, "psi_AA": 1, "psi_AB": 1 + d_H1,
           "c_A": 1 + 2 * d_H1, "c_B": 2 + 2 * d_H1, "c_C": 3 + 2 * d_H1}
    n_scalar = 4 + 2 * d_H1

    def slot_row(slot, d):
        e = [0, 0, 0]
        e[slot] = d
        return ring.index[tuple(e)]

    maps = {}
    for orbit in ("AAA", "AAB", "ABC"):
        A = [[F0] * n_scalar for _ in range(qm.nmon)]
        hconst = [F0] * qm.nmon
        keys, cvar = qm.lam_spec[orbit]
        for slot in range(3):
            key = keys[slot]
            if key == "AA_in":
                for d in range(d_H1):
                    A[slot_row(slot, d)][lay["psi_AA"] + d] += F1
            elif key == "AB_in":
                for d in range(d_H1):
                    A[slot_row(slot, d)][lay["psi_AB"] + d] += F1
            elif key == "AA_out":
                for d in range(d_H1):
                    A[slot_row(slot, d)][lay["psi_AA"] + d] -= Fraction(1, 6)
                    hconst[slot_row(slot, d)] += h_AA[d] / 6
            else:                                            # AB_out
                for d in range(d_H1):
                    A[slot_row(slot, d)][lay["psi_AB"] + d] -= Fraction(4, 3)
                    hconst[slot_row(slot, d)] += h_AB[d] / 3
        A[ring.index[(0, 0, 0)]][lay[cvar]] -= F1
        # F 列（未对称化：全部有序 (a,b)，与 qm.lam 逐列一致）
        AF = []
        for k in range(qm.K):
            mk = qm.F_sizes[k]
            Mk = [[F0] * (mk * mk) for _ in range(qm.nmon)]
            for idx in range(len(qm.Y_cols)):
                kk, a_, b_ = qm.col_kab[idx]
                if kk != k:
                    continue
                col = list(qm.K_cols[idx])
                for slot in range(3):
                    g = qm.GM_OF[keys[slot]]
                    if g:
                        col = [x + g * y for x, y in zip(
                            col, ring.lift_slot0(qm.gm_cols[idx], slot))]
                for p in range(qm.nmon):
                    if col[p]:
                        Mk[p][a_ * mk + b_] += col[p]
            AF.append(Mk)
        AG = []
        for k in range(qm.K):
            mk = mm.sizes[k]
            Mg = [[F0] * (mk * mk) for _ in range(qm.nmon)]
            for a in range(mk):
                for b in range(mk):
                    Rv = mm.R[k][a][b]
                    for p in range(qm.nmon):
                        if Rv[p]:
                            Mg[p][a * mk + b] += Rv[p]
            AG.append(Mg)
        AS = []
        for name, gnz, mons in qm.sos_def:
            m = len(mons)
            Ms_ = [[F0] * (m * m) for _ in range(qm.nmon)]
            for p_ in range(m):
                ep = mons[p_]
                for q_ in range(m):
                    eq = mons[q_]
                    base = (ep[0] + eq[0], ep[1] + eq[1], ep[2] + eq[2])
                    for (eg, cg) in gnz:
                        r = ring.index[(base[0] + eg[0], base[1] + eg[1],
                                        base[2] + eg[2])]
                        Ms_[r][p_ * m + q_] += cg
            AS.append((name, m, Ms_))
        maps[orbit] = dict(A=A, hconst=hconst, AF=AF, AG=AG, AS=AS)
    # 归一化行：3c_A+54c_B+27c_C − e − 9ΣF₀ == 0
    nrm = [F0] * n_scalar
    nrm[lay["e"]] -= F1
    nrm[lay["c_A"]] += qm.nrm["c_A"]
    nrm[lay["c_B"]] += qm.nrm["c_B"]
    nrm[lay["c_C"]] += qm.nrm["c_C"]
    nrmF0 = -Fraction(qm.s111_factor)
    return dict(lay=lay, n_scalar=n_scalar, orbits=maps, nrm=nrm, nrmF0=nrmF0,
                F_sizes=qm.F_sizes, G_sizes=mm.sizes, nmon=qm.nmon)


def validate_cap_maps(qm: QuotientMaps, mm: MomentMaps, maps: dict, rng) -> dict:
    """随机有理数据上逐行核对：hconst + A·x + ΣAF·vecF − ΣAG·vecG − ΣAS·vecB ==
    λ′_orbit − SOS（moment_lam 独立装配）。任何映射错位在此暴露。"""
    ring = qm.ring
    data = random_data_with_G(qm, rng)
    dy = minorant_for(qm.M)
    h_AA = pad_h(dy["coeffs"], qm.d_H)
    data["h_AA"] = list(h_AA)
    data["h_AB"] = list(h_AA)
    B = {}
    for orbit in ("AAA", "AAB", "ABC"):
        for name, _g, _m in qm.sos_def:
            m_ = len(_m)
            Gm = [[Fraction(rng.randint(-6, 6), 4) for _ in range(m_)] for _ in range(m_)]
            B[f"{orbit}_{name}"] = [[sum(Gm[i][t] * Gm[j][t] for t in range(m_))
                                     for j in range(m_)] for i in range(m_)]
    lay, nsc = maps["lay"], maps["n_scalar"]
    x = [F0] * nsc
    x[lay["e"]] = data["e"]
    for nm, key in (("psi_AA", "psi_AA"), ("psi_AB", "psi_AB")):
        for d in range(qm.d_H + 1):
            x[lay[nm] + d] = data[key][d]
    for nm in ("c_A", "c_B", "c_C"):
        x[lay[nm]] = data[nm]
    for orbit in ("AAA", "AAB", "ABC"):
        mp = maps["orbits"][orbit]
        val = [mp["hconst"][p] + sum(mp["A"][p][j] * x[j] for j in range(nsc))
               for p in range(qm.nmon)]
        for k in range(qm.K):
            mk = qm.F_sizes[k]
            for a in range(mk):
                for b in range(mk):
                    gF = data["F"][k][a][b]
                    gG = data["G"][k][a][b]
                    if gF or gG:
                        val = [val[p] + gF * mp["AF"][k][p][a * mk + b]
                               - gG * mp["AG"][k][p][a * mk + b]
                               for p in range(qm.nmon)]
        sos = qm.sos_sum({nm: B[f"{orbit}_{nm}"] for (nm, _g, _m) in qm.sos_def})
        # AS 映射独立核对：Σ_blocks AS_block @ vec(B_block) == qm.sos_sum(B)
        sos_map = [F0] * qm.nmon
        for (name, m, Ms_) in maps["orbits"][orbit]["AS"]:
            Bm = B[f"{orbit}_{name}"]
            for i in range(m):
                for j in range(m):
                    c = Bm[i][j]
                    if c == 0:
                        continue
                    for p in range(qm.nmon):
                        v = Ms_[p][i * m + j]
                        if v:
                            sos_map[p] += c * v
        assert sos_map == sos, f"SOS 映射与 sos_sum 不一致（{orbit}）"
        lamv = moment_lam(qm, mm, orbit, data)
        assert val == lamv, f"cap 映射与 moment_lam 不一致（{orbit}）"
    # 归一化行
    nv = (sum(maps["nrm"][j] * x[j] for j in range(nsc))
          + maps["nrmF0"] * sum(sum(r) for r in data["F"][0]))
    expect = (qm.nrm["c_A"] * data["c_A"] + qm.nrm["c_B"] * data["c_B"]
              + qm.nrm["c_C"] * data["c_C"] + qm.nrm["e"] * data["e"]
              - Fraction(qm.s111_factor) * sum(sum(r) for r in data["F"][0]))
    assert nv == expect == 0, "归一化行映射不一致"
    return dict(ok=True, rows=3 * qm.nmon + 1)


def _fnp(mat):
    import numpy as np
    return np.array([[float(x) for x in row] for row in mat], dtype=float)


def build_cap_sdp_cvxpy(qm: QuotientMaps, maps: dict, with_containers: bool):
    import numpy as np
    import cvxpy as cp
    d_H1 = qm.d_H + 1
    e = cp.Variable(name="e")
    psi_AA = cp.Variable(d_H1, name="psi_AA")
    psi_AB = cp.Variable(d_H1, name="psi_AB")
    cvar = cp.Variable(3, name="c")
    Fs = [cp.Variable((mk, mk), symmetric=True, name=f"F{k}")
          for k, mk in enumerate(maps["F_sizes"])]
    cons = [F >> 0 for F in Fs]
    Gs = []
    if with_containers:
        Gs = [cp.Variable((mk, mk), symmetric=True, name=f"G{k}")
              for k, mk in enumerate(maps["G_sizes"])]
        cons += [G >> 0 for G in Gs]
    xvec = cp.hstack([e, psi_AA, psi_AB, cvar])
    Bhandles = {}
    for orbit in ("AAA", "AAB", "ABC"):
        mp = maps["orbits"][orbit]
        A = _fnp(mp["A"])
        hconst = np.array([float(v) for v in mp["hconst"]])
        expr = A @ xvec + hconst
        for k in range(qm.K):
            expr = expr + _fnp(mp["AF"][k]) @ cp.vec(Fs[k], order="C")
            if with_containers:
                expr = expr - _fnp(mp["AG"][k]) @ cp.vec(Gs[k], order="C")
        sos = np.zeros(maps["nmon"])
        for (name, m, Ms_) in mp["AS"]:
            Bv = cp.Variable((m, m), symmetric=True, name=f"B_{orbit}_{name}")
            cons.append(Bv >> 0)
            expr = expr - _fnp(Ms_) @ cp.vec(Bv, order="C")
            Bhandles[f"{orbit}_{name}"] = Bv
        cons.append(expr == 0)
    nrm = np.array([float(v) for v in maps["nrm"]])
    expr = nrm @ xvec + maps["nrmF0"] * cp.sum(Fs[0])
    cons.append(expr == 0)
    prob = cp.Problem(cp.Maximize(e), cons)
    return prob, dict(e=e, psi_AA=psi_AA, psi_AB=psi_AB, c=cvar, F=Fs, G=Gs,
                      B=Bhandles)


def solve_tier(qm: QuotientMaps, mm: MomentMaps, maps: dict, with_containers: bool,
               tol=1e-9, max_iter=4000, time_limit=2400.0):
    import numpy as np
    prob, V = build_cap_sdp_cvxpy(qm, maps, with_containers)
    t0 = time.time()
    prob.solve(solver="CLARABEL", verbose=False, tol_gap_abs=tol, tol_gap_rel=tol,
               tol_feas=tol, max_iter=max_iter, time_limit=time_limit)
    solve_s = time.time() - t0
    e_val = float(V["e"].value) if V["e"].value is not None else float("nan")
    # 块最小特征值（PSD 残缺量级）＋恒等式残差（λ′ − SOS 应 ~求解器容差）
    min_eig, resid = {}, {}
    xvec = np.concatenate(
        [np.asarray(V["e"].value).ravel(),
         np.asarray(V["psi_AA"].value).ravel(),
         np.asarray(V["psi_AB"].value).ravel(),
         np.asarray(V["c"].value).ravel()])
    for orbit in ("AAA", "AAB", "ABC"):
        mp = maps["orbits"][orbit]
        val = _fnp(mp["A"]) @ xvec + np.array([float(v) for v in mp["hconst"]])
        for k in range(qm.K):
            Fv = np.asarray(V["F"][k].value)
            val = val + _fnp(mp["AF"][k]) @ Fv.reshape(-1, order="C")
            min_eig[f"F{k}"] = float(np.linalg.eigvalsh((Fv + Fv.T) / 2).min())
            if with_containers:
                Gv = np.asarray(V["G"][k].value)
                val = val - _fnp(mp["AG"][k]) @ Gv.reshape(-1, order="C")
                min_eig[f"G{k}"] = float(np.linalg.eigvalsh((Gv + Gv.T) / 2).min())
        sos = np.zeros(qm.nmon)
        for (name, m, Ms_) in mp["AS"]:
            Bv = np.asarray(V["B"][f"{orbit}_{name}"].value)
            sos += _fnp(Ms_) @ Bv.reshape(-1, order="C")
            min_eig[f"B_{orbit}_{name}"] = float(np.linalg.eigvalsh(
                (Bv + Bv.T) / 2).min())
        resid[orbit] = float(np.abs(val - sos).max())
    info = dict(variant="containers" if with_containers else "baseline",
                e_val=e_val, solve_s=round(solve_s, 2),
                status=str(prob.status), iters=(prob.solver_stats.num_iters
                                                if prob.solver_stats else None),
                min_eig=float(min(min_eig.values())),
                identity_residual=max(resid.values()),
                min_eig_by_block={k2: v for k2, v in sorted(min_eig.items())},
                tol=tol)
    return info, V


def build_anchored_sdp(qm: QuotientMaps, maps: dict, with_containers: bool,
                       Gram_ttp, types=(0, 0, 0, 1, 1, 1, 2, 2, 2),
                       groups=("lambda", "kernel")):
    """锚定可行性 SDP（KLT 命题 4.3 等号条款的浮点探针，可分组）。

    groups 子集选择锚定约束组：
      "lambda"：TTP 的 84 个无序三元组处 λ′_cls = 0（逐三元组 SOS 项为零）；
      "kernel"：Σ_all(TTP) = ⟨F,Ñ_k⟩ = 0 ＋ Σ⟨G,M_k(TTP)⟩ = 0。
    全组＝KLT 等号结构：恒等式 (∗) 在 TTP 给 ΣH(TTP) − e = 0 ⟹ e = E*。"""
    import numpy as np
    import cvxpy as cp
    prob, V = build_cap_sdp_cvxpy(qm, maps, with_containers)
    cons = list(prob.constraints)
    ring = qm.ring
    xvec = cp.hstack([V["e"], V["psi_AA"], V["psi_AB"], V["c"]])
    lam_expr = {}
    if "lambda" in groups:
        for orbit in ("AAA", "AAB", "ABC"):
            mp = maps["orbits"][orbit]
            expr = _fnp(mp["A"]) @ xvec + np.array([float(v) for v in mp["hconst"]])
            for k in range(qm.K):
                expr = expr + _fnp(mp["AF"][k]) @ cp.vec(V["F"][k], order="C")
                if with_containers:
                    expr = expr - _fnp(mp["AG"][k]) @ cp.vec(V["G"][k], order="C")
            for (name, m, Ms_) in mp["AS"]:
                expr = expr - _fnp(Ms_) @ cp.vec(V["B"][f"{orbit}_{name}"], order="C")
            lam_expr[orbit] = expr

    def powers(u, v, t):
        out = np.zeros(qm.nmon)
        for p, (i, j, l) in enumerate(ring.mons):
            out[p] = (u ** i) * (v ** j) * (t ** l)
        return out

    n_anchor = 0
    if "lambda" in groups:
        orbit_of = {cls: orbit for (cls, orbit, _p) in qm.full_classes}
        perm_of = {cls: p for (cls, _o, p) in qm.full_classes}
        for (i, j, l) in combinations(range(N), 3):
            tt = sorted([(types[i], i), (types[j], j), (types[l], l)])
            (_r0, i0), (_r1, j0), (_r2, l0) = tt
            cls = tuple(x2[0] for x2 in tt)
            u, v, t = float(Gram_ttp[i0][j0]), float(Gram_ttp[i0][l0]), float(Gram_ttp[j0][l0])
            if perm_of[cls] == "ut":
                u, t = t, u
            pv = powers(u, v, t)
            cons.append(pv @ lam_expr[orbit_of[cls]] == 0)
            n_anchor += 1
    if "kernel" in groups:
        GramF = [[x if isinstance(x, Fraction) else Fraction(str(round(float(x), 12)))
                  for x in row] for row in Gram_ttp]
        Nk = M_kernel_exact(qm, GramF)
        for k in range(qm.K):
            Nf = np.array([[float(x) for x in row] for row in Nk[k]])
            cons.append(cp.sum(cp.multiply(Nf, V["F"][k])) == 0)
            if with_containers:
                cons.append(cp.sum(cp.multiply(Nf, V["G"][k])) == 0)
        n_anchor += 2 * qm.K
    aprob = cp.Problem(cp.Maximize(V["e"]), cons)
    return aprob, V, n_anchor


def run_anchored_probe(tiers=None, spot_seed=SEED, decompose_tier=(7, 6)):
    """锚定探针：全组（KLT 等号结构）各档两臂＋末档分组分解（λ 侧 vs 核侧）。

    Clarabel 数值失败时降级 SCS（eps 1e-7）；求解器失败如实记 status（不可行/
    数值退化的判读见 results/moment_lift.json 的 mechanistic 结论）。"""
    import numpy as np
    sys.path.insert(0, str(HERE.parent))
    from family import tri_cap_prism
    z = 0.5 * (Z_STAR_INTERVAL[0] + Z_STAR_INTERVAL[1])
    X = tri_cap_prism(z)
    Gm = X @ X.T
    if tiers is None:
        tiers = [(6, 6), (7, 6)]
    lo = Fraction(-187, 250)
    rng = random.Random(spot_seed)
    results = []

    def solve_rec(qm, maps, wc, Gm, groups, label, row):
        import cvxpy as cp
        t0 = time.time()
        rec = dict(groups=list(groups), arm="containers" if wc else "baseline")
        try:
            aprob, V, n_anchor = build_anchored_sdp(qm, maps, wc, Gm, groups=groups)
            rec["n_anchor_constraints"] = n_anchor
            try:
                aprob.solve(solver="CLARABEL", verbose=False, tol_gap_abs=1e-9,
                            tol_gap_rel=1e-9, tol_feas=1e-9, max_iter=8000,
                            time_limit=1500.0)
                rec["solver"] = "CLARABEL"
            except Exception:
                aprob.solve(solver="SCS", verbose=False, eps=1e-7, max_iters=20000,
                            time_limit_secs=1500.0)
                rec["solver"] = "SCS(fallback)"
            e_val = float(V["e"].value) if V["e"].value is not None else float("nan")
            rec.update(e_val=e_val, status=str(aprob.status),
                       dist_to_E_star=float(E_TTP_TUBE) - e_val,
                       solve_s=round(time.time() - t0, 1))
        except Exception as exc:                      # noqa: BLE001
            rec.update(status=f"solver_error:{type(exc).__name__}", error=str(exc),
                       solve_s=round(time.time() - t0, 1))
        row[label] = rec
        print(f"[anchored] ({row['M']},{row['K']}) {label}/{rec['arm']}: "
              f"e={rec.get('e_val', float('nan'))!s} status={rec['status']} "
              f"E*−e={rec.get('dist_to_E_star', float('nan'))!s}", flush=True)

    for (M, K) in tiers:
        qm = QuotientMaps(lo, M, K)
        mm = MomentMaps(qm)
        dy = minorant_for(M)
        h_AA = pad_h(dy["coeffs"], qm.d_H)
        maps = build_cap_maps(qm, mm, h_AA, h_AA)
        row = dict(M=M, K=K)
        for wc in (False, True):
            solve_rec(qm, maps, wc, Gm, ("lambda", "kernel"),
                      "anchored_containers" if wc else "anchored_baseline", row)
        if (M, K) == tuple(decompose_tier):
            solve_rec(qm, maps, True, Gm, ("lambda",), "decomp_lambda_only", row)
            solve_rec(qm, maps, True, Gm, ("kernel",), "decomp_kernel_only", row)
            # 机制补充：TTP 矩矩阵 Ñ_k 的秩结构（核侧锚定的结构性可行性）
            GramF = [[Fraction(str(round(float(x), 12))) for x in row2] for row2 in Gm]
            Nk = M_kernel_exact(qm, GramF)
            import numpy as _np
            row["ttp_moment_matrix_ranks"] = [
                dict(k=k, size=qm.F_sizes[k],
                     rank=int((_np.linalg.eigvalsh(_np.array(
                         [[float(x) for x in r] for r in Nk[k]])) > 1e-8).sum()))
                for k in range(qm.K)]
        results.append(row)
    return results


def recompute_verdict(results: list, anchored: list) -> dict:
    """判死活（单一事实源；run_probe 与归档合并共用）。

    噪声地板的诚实口径＝max over 档 of max(臂内跨容差 |Δe|, max(0,−Δ_tier))：
    容器臂可行集 ⊇ 基线臂（G=0 复现基线）⟹ 真值 Δ≥0 恒成立，实测 Δ<0 的幅度
    是两臂合并求解器误差的**下界**（(6,6) 实测 −8.5e-7 即此）——用它做全局地板
    对 false-alive 保守。alive 另需末档 Δ 不比前档退化一个量级；锚定探针
    e_val 达 |E*−e|≤1e-6 为 alive 强证据（KLT 等号结构可达）。"""
    effective = []
    for r in results:
        arm = max(r.get("arm_noise", {}).get("baseline", 0.0),
                  r.get("arm_noise", {}).get("containers", 0.0))
        effective.append(max(arm, max(0.0, -r["delta_e_val"])))
    global_noise = max(effective) if effective else 0.0
    alive_votes, deltas = [], []
    for r in results:
        ok = (r["delta_e_val"] > max(global_noise, 1e-10))
        alive_votes.append(ok)
        deltas.append(r["delta_e_val"])
    alive = all(alive_votes) and len(deltas) >= 2 and \
        deltas[-1] >= 0.1 * max(deltas[:-1] + [1e-300])
    anchored_ok = None
    if anchored and isinstance(anchored[-1], dict) and "error" not in anchored[-1]:
        # 有效性口径：锚定 SDP 任何可行点 e ≤ E*（证书有效域含 TTP）⟹ e_val 超界
        # 即求解器发散垃圾（status≠optimal 一并排除）；alive 强证据需收敛且 |E*−e|≤1e-6
        cands = []
        for a in anchored:
            if not isinstance(a, dict):
                continue
            for key in ("anchored_containers", "anchored_baseline",
                        "decomp_lambda_only", "decomp_kernel_only"):
                rec = a.get(key)
                if not isinstance(rec, dict):
                    continue
                e_v, st = rec.get("e_val"), rec.get("status", "")
                if (e_v is not None and st == "optimal"
                        and float(e_v) <= float(E_TTP_TUBE) + 1e-6):
                    cands.append(float(e_v))
        best = max(cands, default=-1e9)
        anchored_ok = float(E_TTP_TUBE) - best <= 1e-6
    return dict(verdict="alive" if (alive or anchored_ok) else "dead",
                alive_votes=alive_votes, deltas=deltas,
                noise_floor_global=float(global_noise),
                noise_floor_by_tier=[float(x) for x in effective],
                anchored_reaches_E_star=anchored_ok,
                rule="alive 需全部档 Δe_val > max(全局噪声地板,1e-10) 且末档 Δ ≥ "
                     "0.1×前档最大 Δ；全局噪声地板＝max over 档 max(臂内跨容差|Δe|, "
                     "max(0,−Δ))（容器可行集⊇基线 ⟹ 真值Δ≥0，实测负Δ为求解器误差"
                     "下界）；或锚定探针 e_val 达 |E*−e|≤1e-6（KLT 等号结构可达，"
                     "alive 强证据）")


def run_probe(tiers=None, out=None, spot_seed=SEED, noise_tol2=1e-11,
              with_anchored=True):
    """相位 A 探针：各 (M,K) 档 baseline vs containers（同档同参数对照）＋噪声地板。

    with_anchored=False 时跳过锚定探针（验收门 ① 的快速重放口径）。"""
    import numpy as np
    if tiers is None:
        tiers = [(6, 6), (7, 6)]
    lo = Fraction(-187, 250)
    rng = random.Random(spot_seed)
    results = []
    for (M, K) in tiers:
        qm = QuotientMaps(lo, M, K)
        mm = MomentMaps(qm)
        dy = minorant_for(M)
        h_AA = pad_h(dy["coeffs"], qm.d_H)
        maps = build_cap_maps(qm, mm, h_AA, h_AA)
        chk = validate_cap_maps(qm, mm, maps, rng)
        info_b, Vb = solve_tier(qm, mm, maps, False)
        info_c, Vc = solve_tier(qm, mm, maps, True)
        # 噪声地板（逐臂）：每臂以更严容差重解一次，臂内 |Δe|＋双臂取 max。
        # （Clarabel 确定性 ⟹ 同设置逐位复现；跨容差差才是求解器实用精度。）
        info_b2, _V2 = solve_tier(qm, mm, maps, False,
                                  tol=1e-11, max_iter=8000, time_limit=2400.0)
        info_c2, _V3 = solve_tier(qm, mm, maps, True,
                                  tol=1e-11, max_iter=8000, time_limit=2400.0)
        noise_b = abs(info_b2["e_val"] - info_b["e_val"])
        noise_c = abs(info_c2["e_val"] - info_c["e_val"])
        noise = max(noise_b, noise_c)
        e_b = max(info_b["e_val"], info_b2["e_val"])
        e_c = max(info_c["e_val"], info_c2["e_val"])
        delta = e_c - e_b
        # TTP 诊断：在 TTP 配置上分解 E−e 的四项（λ′ 最小、Σ_all、Σ⟨G,M⟩、恒等式残差）
        diag = ttp_diagnostics(qm, mm, maps, info_c, Vc, with_containers=True)
        diag_b = ttp_diagnostics(qm, mm, maps, info_b, Vb, with_containers=False)
        results.append(dict(M=M, K=K, minorant_nodes=len(dy["nodes"]),
                            minorant_W=str(dy["W"]),
                            baseline=info_b, containers=info_c,
                            baseline_rerun_tight=info_b2,
                            containers_rerun_tight=info_c2,
                            e_val_baseline_best=float(e_b),
                            e_val_containers_best=float(e_c),
                            arm_noise=dict(baseline=float(noise_b),
                                           containers=float(noise_c)),
                            delta_e_val=float(delta), noise_floor=float(noise),
                            ttp=diag, ttp_baseline=diag_b, maps_check=chk))
        print(f"[probe] ({M},{K}): baseline e={e_b:.12f} "
              f"containers e={e_c:.12f} Δ={delta:+.3e} "
              f"noise={noise:.2e} ({info_c['solve_s']}s/{info_b['solve_s']}s)", flush=True)
    # 锚定可行性探针（判死活的机制性证据：等号结构可达性——只对最大档做
    # 全组＋分组分解，控时间；小档锚定失败证据已由 (5,4) 冒烟验证同型）
    if not with_anchored:
        anchored = []
    else:
        try:
            anchored = run_anchored_probe(tiers=[tiers[-1]], spot_seed=spot_seed)
        except Exception as exc:                   # noqa: BLE001
            anchored = [dict(error=str(exc))]
            print(f"[anchored] 失败：{exc}", flush=True)
    # 判死活（单一事实源 recompute_verdict；归档合并时复算同一规则）
    verdict = recompute_verdict(results, anchored)
    outd = dict(kind="moment-lift-probe", seed=spot_seed,
                code_version=code_version(),
                generated=datetime.now(timezone.utc).isoformat(timespec="seconds"),
                tiers=results, anchored=anchored, verdict=verdict,
                a0=str(lo), minorant_k=48,
                minorant_policy="minorant_for(M)：6 节点（deg 11）需 d_H≥11（M≥7）；"
                                "(6,6) 档 d_H=10 放不下 ⟹ 5 节点（deg 9，去最大节点 ν₆），"
                                "双臂同参对照仍成立（Δ 为同 (M,K) 同 minorant 差）")
    if out is not None:
        p = Path(out)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(outd, indent=1, default=str) + "\n")
    return outd


def ttp_diagnostics(qm: QuotientMaps, mm: MomentMaps, maps: dict, info: dict, V,
                    with_containers: bool):
    """TTP 配置上恒等式 (∗) 逐项数值分解：E_ttp−e = Σ_T λ′_T + Σ_all + Σ⟨G,M⟩。

    λ′ 系数向量由 solve_tier 的解数据数值重建（映射 hconst+A+AF−AG），三元组
    求值走 float（诊断口径，非认证）；类锚定＝排序后槽序（与恒等式自检同口径）。"""
    import numpy as np
    sys.path.insert(0, str(HERE.parent))
    from family import tri_cap_prism
    z = 0.5 * (Z_STAR_INTERVAL[0] + Z_STAR_INTERVAL[1])
    X = tri_cap_prism(z)
    Gm = X @ X.T
    types = [0] * 3 + [1] * 3 + [2] * 3          # 上棱/下棱/帽（family.py 顺序）
    e_val = info["e_val"]
    psi_AA = np.asarray(V["psi_AA"].value).ravel()
    psi_AB = np.asarray(V["psi_AB"].value).ravel()
    cv = np.asarray(V["c"].value).ravel()
    Fs = [np.asarray(F.value) for F in V["F"]]
    Gs = [np.asarray(G.value) for G in V["G"]] if with_containers else None
    ring = qm.ring

    def ev(vec, u, v, t):
        pu = [1.0] + [0.0] * qm.D
        pv = [1.0] + [0.0] * qm.D
        pt = [1.0] + [0.0] * qm.D
        for i in range(1, qm.D + 1):
            pu[i] = pu[i - 1] * u
            pv[i] = pv[i - 1] * v
            pt[i] = pt[i - 1] * t
        return sum(c * pu[i] * pv[j] * pt[l]
                   for c, (i, j, l) in zip(vec, ring.mons) if c)

    lam_vecs = {}
    for orbit in ("AAA", "AAB", "ABC"):
        mp = maps["orbits"][orbit]
        vec = np.zeros(qm.nmon)
        for p in range(qm.nmon):
            row = mp["A"][p]
            acc = float(mp["hconst"][p])
            acc += (row[0] * e_val
                    + float(np.dot(np.asarray(row[1:1 + qm.d_H + 1], dtype=float),
                                   psi_AA))
                    + float(np.dot(np.asarray(row[1 + qm.d_H + 1:1 + 2 * (qm.d_H + 1)],
                                              dtype=float), psi_AB))
                    + row[-3] * float(cv[0]) + row[-2] * float(cv[1])
                    + row[-1] * float(cv[2]))
            vec[p] = acc
        for k in range(qm.K):
            mk = qm.F_sizes[k]
            for a in range(mk):
                for b in range(mk):
                    gF = float(Fs[k][a][b])
                    if gF:
                        vec = [vv + gF * float(mp["AF"][k][p2][a * mk + b])
                               for p2, vv in enumerate(vec)]
                    if with_containers:
                        gG = float(Gs[k][a][b])
                        if gG:
                            vec = [vv - gG * float(mp["AG"][k][p2][a * mk + b])
                                   for p2, vv in enumerate(vec)]
        lam_vecs[orbit] = list(vec)
    # Σ_T λ′（无序不同三元组，类锚定＝排序后 (i0,j0,l0) 槽序）
    sum_lam, min_lam = 0.0, float("inf")
    orbit_of = {cls: orbit for (cls, orbit, _p) in qm.full_classes}
    for (i, j, l) in combinations(range(N), 3):
        tt = sorted([(types[i], i), (types[j], j), (types[l], l)])
        (_r0, i0), (_r1, j0), (_r2, l0) = tt
        cls = tuple(x2[0] for x2 in tt)
        val = ev(lam_vecs[orbit_of[cls]], float(Gm[i0][j0]),
                 float(Gm[i0][l0]), float(Gm[j0][l0]))
        sum_lam += val
        min_lam = min(min_lam, val)
    # Σ_all（有序含重复）：s = Σ⟨F,Y⟩
    s_vec = [0.0] * qm.nmon
    for k in range(qm.K):
        mk = qm.F_sizes[k]
        for a in range(mk):
            for b in range(mk):
                gF = float(Fs[k][a][b])
                if gF:
                    Yc = qm.Y_cols[qm.Y_index[(k, a, b)]]
                    s_vec = [sv + gF * float(y) for sv, y in zip(s_vec, Yc)]
    sum_all = sum(ev(s_vec, float(Gm[i][j]), float(Gm[i][l]), float(Gm[j][l]))
                  for i in range(N) for j in range(N) for l in range(N))
    # Σ⟨G,M⟩（ζ 口径 float）
    sum_cont = 0.0
    if with_containers:
        Ms = zeta_M_float(qm, X)
        for k in range(qm.K):
            Gk = (Gs[k] + Gs[k].T) / 2
            sum_cont += float((Gk * Ms[k]).sum())
    E_ttp = float(E_TTP_TUBE)
    return dict(e_val=e_val, E_ttp=E_ttp, gap=E_ttp - e_val,
                sum_lambda_prime=sum_lam, min_lambda_prime=min_lam,
                sum_all=sum_all, sum_container_moments=sum_cont,
                identity_resid=abs(sum_lam + sum_all + sum_cont
                                   - (E_ttp - e_val)))


# ============================================================ 相位 B：SDPA 导出
def export_row_check_moment(qm: QuotientMaps, mm: MomentMaps, ex: MomentCapExporter,
                            rng) -> dict:
    """随机变量赋值上逐行核对 SDPA 条目：func(row) − b[row] == λ′_orbit − SOS
    （moment_lam 独立装配）。G 块的行/符号/常数错位在此暴露（防白跑笼子，
    hermite_ladder.export_row_check_cap 的容器版）。"""
    from hermite_ladder import _row_functional
    d_H1 = qm.d_H + 1
    psi_AA = [Fraction(rng.randint(-9, 9), 7) for _ in range(d_H1)]
    psi_AB = [Fraction(rng.randint(-9, 9), 7) for _ in range(d_H1)]
    cvals = {n: Fraction(rng.randint(-9, 9), 7) for n in ("c_A", "c_B", "c_C")}
    lp_vals = {ex.e_pos: Fraction(25, 1)}
    for name, vec in (("psi_AA", psi_AA), ("psi_AB", psi_AB)):
        pp, mmn = ex.vpos[name]
        for d in range(d_H1):
            lp_vals[pp + d] = vec[d]
            lp_vals[mmn + d] = F0
    for name in cvals:
        pp, mmn = ex.vpos[name]
        lp_vals[pp] = cvals[name]
        lp_vals[mmn] = F0
    mat_vals, F_list, G_list = {}, [], []
    for kk, mk in enumerate(qm.F_sizes):
        Gm = [[Fraction(rng.randint(-6, 6), 4) for _ in range(mk)] for _ in range(mk)]
        Fk = [[sum(Gm[i][t] * Gm[j][t] for t in range(mk)) for j in range(mk)]
              for i in range(mk)]
        F_list.append(Fk)
        mat_vals[ex.f_off + kk] = Fk
    for kk, mk in enumerate(mm.sizes):
        Gm = [[Fraction(rng.randint(-6, 6), 4) for _ in range(mk)] for _ in range(mk)]
        Gk = [[sum(Gm[i][t] * Gm[j][t] for t in range(mk)) for j in range(mk)]
              for i in range(mk)]
        G_list.append(Gk)
        mat_vals[ex.g_off + kk] = Gk
    B = {}
    for oi, orbit in enumerate(("AAA", "AAB", "ABC")):
        for bi, (name, _g, mons) in enumerate(qm.sos_def):
            m_ = len(mons)
            Gm = [[Fraction(rng.randint(-6, 6), 4) for _ in range(m_)] for _ in range(m_)]
            Bm = [[sum(Gm[i][t] * Gm[j][t] for t in range(m_)) for j in range(m_)]
                  for i in range(m_)]
            B[f"{orbit}_{name}"] = Bm
            mat_vals[ex.sos_off + oi * len(qm.sos_def) + bi] = Bm
    func = _row_functional(ex.build_entries(), lp_vals, mat_vals)
    b = ex.b_vector()
    data = dict(h_AA=ex.h_AA, h_AB=ex.h_AB, psi_AA=psi_AA, psi_AB=psi_AB,
                c_A=cvals["c_A"], c_B=cvals["c_B"], c_C=cvals["c_C"],
                e=lp_vals[ex.e_pos], F=F_list, G=G_list, B=B)
    checked = 0
    for orbit in ("AAA", "AAB", "ABC"):
        lv = moment_lam(qm, mm, orbit, data)
        sv = qm.sos_sum({nm: B[f"{orbit}_{nm}"] for (nm, _g, _m) in qm.sos_def})
        row0 = ex.orbit_row[orbit]
        for p in range(qm.nmon):
            lhs = func.get(row0 + p, F0) - b[row0 + p - 1]
            if lhs != lv[p] - sv[p]:
                fail(f"moment cap 导出行泛函不一致：{orbit} mon #{p}: "
                     f"{lhs} ≠ {lv[p] - sv[p]}")
            checked += 1
    return dict(rows_checked=checked, ok=True)


class MomentCapExporter(HermiteCapExporter):
    """HermiteCapExporter ＋矩容器 G 块：blk 布局 [LP, F×K, G×K, SOS×3×8]。

    行约束变为 λ − Σ⟨G,R⟩ − SOS = 0（b 不变＝−h 份额；容器不入 b/归一化）。"""

    def __init__(self, qm: QuotientMaps, mm: MomentMaps, h_AA, h_AB,
                 lp_penalty=Fraction(1, 10 ** 11)):
        self.mm = mm
        super().__init__(qm, h_AA, h_AB, lp_penalty=lp_penalty)
        self.blk = ([-self.n_lp] + list(qm.F_sizes) + list(mm.sizes)
                    + [len(m) for _n, _g, m in qm.sos_def] * 3)
        self.g_off = self.f_off + len(qm.F_sizes)
        self.sos_off = self.g_off + len(mm.sizes)

    def _slack_rows(self, orbit):
        E = super()._slack_rows(orbit)
        row0 = self.orbit_row[orbit]
        qm = self.qm
        for k in range(self.mm.K):
            l = self.g_off + k
            mk = self.mm.sizes[k]
            Rk = self.mm.R[k]
            for a_ in range(mk):
                for b_ in range(a_, mk):
                    col = Rk[a_][b_]
                    if a_ == b_:
                        for p, c in enumerate(col):
                            if c:
                                E.append((row0 + p, l, a_ + 1, a_ + 1, -c))
                    else:
                        for p, c in enumerate(col):
                            if c:
                                E.append((row0 + p, l, a_ + 1, b_ + 1, -c))
        return E

    def write_dat(self, path: Path):
        E = self.build_entries()
        b = self.b_vector()
        with open(path, "w") as f:
            f.write('"N=9 typed (3,3,3) S3-quotient Hermite-fixed + moment-container cap SDP (exact rational)"\n')
            f.write(f"{self.m} = mDIM\n{len(self.blk)} = nBLOCK\n")
            f.write(" ".join(str(s) for s in self.blk) + " = bLOCKsTRUCT\n")
            f.write(" ".join(frac_dec(x) for x in b) + "\n")
            for (k, l, i, j, v) in E:
                f.write(f"{k} {l} {i} {j} {frac_dec(v)}\n")
        return self.m, len(E)


def solution_from_parse_moment(ex: MomentCapExporter, parsed: dict, h_AA, h_AB):
    qm, mm = ex.qm, ex.mm
    lp = parsed["lp"]
    if len(lp) != ex.n_lp:
        fail(f"LP 块长度 {len(lp)} ≠ {ex.n_lp}")
    d_H1 = qm.d_H + 1

    def split_get(name):
        pp, mm_ = ex.vpos[name]
        return [lp[pp - 1 + d] - lp[mm_ - 1 + d] for d in range(d_H1)]

    def split_scal(name):
        pp, mm_ = ex.vpos[name]
        return lp[pp - 1] - lp[mm_ - 1]

    data = dict(h_AA=list(h_AA), h_AB=list(h_AB),
                psi_AA=split_get("psi_AA"), psi_AB=split_get("psi_AB"),
                c_A=split_scal("c_A"), c_B=split_scal("c_B"),
                c_C=split_scal("c_C"), e=lp[ex.e_pos - 1])
    mats = []
    for g in parsed["sdp"]:
        n = len(g)
        if any(len(r) != n for r in g):
            fail("SDP 块非方阵")
        mats.append([[Fraction(x) for x in r] for r in g])
    n_expect = len(qm.F_sizes) + len(mm.sizes) + 3 * len(qm.sos_def)
    if len(mats) != n_expect:
        fail(f"SDP 块数 {len(mats)} ≠ {n_expect}")
    off = 0
    data["F"] = mats[off:off + len(qm.F_sizes)]
    off += len(qm.F_sizes)
    data["G"] = mats[off:off + len(mm.sizes)]
    off += len(mm.sizes)
    B = {}
    for oi, orbit in enumerate(("AAA", "AAB", "ABC")):
        for bi, (name, _g, mons) in enumerate(qm.sos_def):
            B[f"{orbit}_{name}"] = mats[off]
            off += 1
    data["B"] = B
    return data


def raw_residuals_moment(qm: QuotientMaps, mm: MomentMaps, data: dict) -> dict:
    R1 = {}
    for orbit in ("AAA", "AAB", "ABC"):
        lv = moment_lam(qm, mm, orbit, data)
        sv = qm.sos_sum({nm: data["B"][f"{orbit}_{nm}"] for (nm, _g, _m) in qm.sos_def})
        R1[orbit] = sum(abs(x - y) for x, y in zip(lv, sv))
    nrm_resid = (qm.nrm["c_A"] * data["c_A"] + qm.nrm["c_B"] * data["c_B"]
                 + qm.nrm["c_C"] * data["c_C"] + qm.nrm["e"] * data["e"]
                 - Fraction(qm.s111_factor) * sum(sum(r) for r in data["F"][0]))
    return dict(R1=R1, nrm=nrm_resid)


# ============================================================ R8-2：锚定精确取等探针（精确行版）
# KLT 命题 4.3 等号证书的判死活探针：把 build_anchored_sdp 的锚定约束改写为
# 精确 Fraction 线性等式行接入 MomentCapExporter（.dat-s 加行、b=0），用
# SDPA-GMP 求解（替换 R7-1 的 SCS optimal_inaccurate 口径）。
SEED_ANCHOR = 20261008
ANCHOR_ROUND_DECIMALS = 12
ANCHOR_TYPES = (0, 0, 0, 1, 1, 1, 2, 2, 2)        # family.tri_cap_prism 顺序：上棱/下棱/帽
E_STAR_9DP = Fraction("25.759986531")             # energies.json 9 位口径（并列判据，D19 裁决 3）
R7_1_SCS_BASELINE = dict(                          # R7-1 (7,6) SCS 基线（入档对照，D19 裁决 3）
    e_val=25.75729578909048, status="optimal_inaccurate", solver="SCS(fallback)",
    groups=["lambda", "kernel"], containers=False,
    dist_to_E_ttp=0.0026907421793502806, n_anchor_constraints=96,
    source="results/moment_lift.json /probe/anchored[0]/anchored_baseline",
    caveat=("lambda 组在 cvxpy 版锚 λ′−SOS（被 base 行蕴含的空约束，D20 留痕）；"
            "optimal_inaccurate 解只是锚定最优值的下界"))


def ttp_anchor_gram(round_decimals: int = ANCHOR_ROUND_DECIMALS):
    """TTP（D3h tricapped prism，z* 隔离区间中点）Gram 的精确有理锚定点。

    纯 math 重实现 family.tri_cap_prism（裸 python3 可用，无 numpy 依赖）；
    每项四舍五入 round_decimals 位十进 → 确定性 Fraction 矩阵（R7-1
    build_anchored_sdp 的 kernel 组同口径 round(x,12)）。identity (∗) 在该
    Gram 上精确成立（对称 Gram 即可，无需 config 性——本会话 precheck 随机
    数据 exact 验证）；E_anchor=ΣH(Gram) 与 E_ttp 差 2.49e-12。"""
    z = 0.5 * (Z_STAR_INTERVAL[0] + Z_STAR_INTERVAL[1])
    rho = math.sqrt(1.0 - z * z)
    pts = []
    for k in range(3):
        pts.append((rho * math.cos(2 * math.pi * k / 3),
                    rho * math.sin(2 * math.pi * k / 3), z))
    for k in range(3):
        pts.append((rho * math.cos(2 * math.pi * k / 3),
                    rho * math.sin(2 * math.pi * k / 3), -z))
    for k in range(3):
        pts.append((math.cos(math.pi / 3 + 2 * math.pi * k / 3),
                    math.sin(math.pi / 3 + 2 * math.pi * k / 3), 0.0))
    Gram = [[Fraction(str(round(sum(a * b for a, b in zip(xi, xj)), round_decimals)))
             for xj in pts] for xi in pts]
    for i in range(N):
        assert Gram[i][i] == 1, "锚定 Gram 对角非 1"
        for j in range(i):
            assert Gram[i][j] == Gram[j][i], "锚定 Gram 非对称"
    return Gram, z


def anchor_sum_H(Gram_ttp, k_minor: int = 48) -> Fraction:
    """Σ_{i<j} h(g_ij)（固定 Hermite minorant，精确）＝锚定可行点的确定性 e 值。

    identity (∗) 在锚定 Gram 上给 ΣH − e = Σ_T λ′ + Σ_all + Σ⟨G,M⟩；锚定行把
    右侧三项全部钉零 ⟹ 任何可行点 e = ΣH(anchor)（M 无关；h 系数对 M≥7 档
    同为 fixed_minorant(k_minor) 零填充）。"""
    h = fixed_minorant(k_minor)["coeffs"]

    def hval(g):
        acc = F0
        for c in reversed(h):
            acc = acc * g + c
        return acc

    return sum(hval(Gram_ttp[i][j]) for i in range(N) for j in range(i + 1, N))


class AnchoredCapExporter(MomentCapExporter):
    """MomentCapExporter/HermiteCapExporter ＋锚定精确等式行（b=0；R8-2）。

    行布局（base 3·nmon slack＋1 归一化 之后追加）：
      「lambda」组：Σ_p pv[p]·SOS_o[p] = 0——base slack 行 SOS 侧条目按 power
        向量 pv（锚定 Gram 三元组 (u,v,t) 的精确幂向量）线性组合。由 base 行
        λ′_o = SOS_o（系数级等式）⟺ λ′_o(x_T) = 0（KLT 等号证书：逐三元组
        非负项为零）。84 个无序不同下标三元组中 (orbit,(u,v,t)) 相同者合并
        导出（TTP 对称性：84→16 行；约束组数学等价，行元数据记完整映射）。
        【修复留痕 D20】R7-1 cvxpy 版误锚 λ′−SOS＝被 base 行蕴含的空约束；
        本类锚 SOS 侧＝真约束。
      「kernel」组：⟨F_k,Ñ_k⟩ = 0 ＋（容器臂）⟨G_k,Ñ_k⟩ = 0，Ñ_k =
        M_k(anchor Gram) 核和口径（M_kernel_exact，精确 Fraction）。Σ_all =
        Σ_k⟨F_k,Ñ_k⟩、Σ⟨G,M⟩ = Σ_k⟨G_k,Ñ_k⟩——逐 k 行蕴含总和为零
        （Ñ_k 秩亏，R7-1 实测 rank 1–2；逐 k 是「每项非负」口径的忠实实现）。
    containers=False（Arm C 诊断）：无 G 块（HermiteCapExporter 布局），λ′ 无
    容器项，kernel 组只有 F 行。"""

    def __init__(self, qm: QuotientMaps, mm: MomentMaps, h_AA, h_AB, Gram_ttp,
                 groups=("lambda", "kernel"), containers=True,
                 lp_penalty=Fraction(1, 10 ** 11)):
        self.anchor_groups = tuple(groups)
        self.containers_flag = bool(containers)
        self.Gram_ttp = Gram_ttp
        if containers:
            super().__init__(qm, mm, h_AA, h_AB, lp_penalty=lp_penalty)
        else:
            HermiteCapExporter.__init__(self, qm, h_AA, h_AB, lp_penalty=lp_penalty)
            self.mm = mm
        self._slack_cache = {}
        self._entries_cache = None
        self._dropped = []
        self.rowmap = None
        self.m_exported = None
        self._build_anchor_rows()

    # ---- 基础行按臂选型（containers=False 走 Hermite 版：无 G 行）----
    def _slack_rows(self, orbit):
        if orbit not in self._slack_cache:
            if self.containers_flag:
                self._slack_cache[orbit] = MomentCapExporter._slack_rows(self, orbit)
            else:
                self._slack_cache[orbit] = HermiteCapExporter._slack_rows(self, orbit)
        return self._slack_cache[orbit]

    # ---- 锚定行构造（精确）----
    def _build_anchor_rows(self):
        qm, ring = self.qm, self.qm.ring
        # lambda 组：84 逻辑约束 → (orbit,(u,v,t)) 合并
        orbit_of = {cls: o for (cls, o, _p) in qm.full_classes}
        perm_of = {cls: p for (cls, _o, p) in qm.full_classes}
        coll, order = {}, []
        for (i, j, l) in combinations(range(N), 3):
            tt = sorted([(ANCHOR_TYPES[i], i), (ANCHOR_TYPES[j], j),
                         (ANCHOR_TYPES[l], l)])
            (_r0, i0), (_r1, j0), (_r2, l0) = tt
            cls = tuple(x[0] for x in tt)
            u, v, t = self.Gram_ttp[i0][j0], self.Gram_ttp[i0][l0], self.Gram_ttp[j0][l0]
            if perm_of[cls] == "ut":
                u, t = t, u
            key = (orbit_of[cls], (u, v, t))
            if key not in coll:
                coll[key] = dict(orbit=key[0], uvw=key[1], cls=cls, triples=[])
                order.append(key)
            coll[key]["triples"].append((i0, j0, l0))
        self.anchor_lambda = [coll[k] for k in order]
        self.anchor_lambda_logical = sum(len(c["triples"]) for c in self.anchor_lambda)
        # kernel 组：Ñ_k = M_k(anchor Gram)（精确核和口径；对称断言）
        self.Nk = M_kernel_exact(qm, self.Gram_ttp)
        for k in range(qm.K):
            mk = qm.F_sizes[k]
            for a in range(mk):
                for b in range(mk):
                    assert self.Nk[k][a][b] == self.Nk[k][b][a], \
                        f"Ñ_{k}[{a}][{b}] 不对称"
        self.anchor_kernel = []
        if "kernel" in self.anchor_groups:
            for k in range(qm.K):
                self.anchor_kernel.append(dict(block="F", k=k))
                if self.containers_flag:
                    self.anchor_kernel.append(dict(block="G", k=k))
        # 行号分配（base m 之后）
        r = self.m + 1
        for c in self.anchor_lambda if "lambda" in self.anchor_groups else []:
            c["row"] = r
            pv = [F0] * qm.nmon
            u, v, t = c["uvw"]
            for p, (a, b, d) in enumerate(ring.mons):
                pv[p] = (u ** a) * (v ** b) * (t ** d)
            c["pv"] = pv
            r += 1
        for c in self.anchor_kernel:
            c["row"] = r
            r += 1
        self.n_anchor_rows = r - self.m - 1
        self.m = r - 1
        self.n_anchor_constraints = (self.anchor_lambda_logical
                                     if "lambda" in self.anchor_groups else 0) \
            + len(self.anchor_kernel)

    def _anchor_entries(self):
        qm = self.qm
        acc: dict = {}

        def put(k, l, i, j, v):
            if v:
                acc[(k, l, i, j)] = acc.get((k, l, i, j), F0) + v

        sos_off = self.sos_off
        if "lambda" in self.anchor_groups:
            sos_side = {}
            for orbit in ("AAA", "AAB", "ABC"):
                row0 = self.orbit_row[orbit]
                sos_side[orbit] = [(p, l, i, j, v) for (rr, l, i, j, v)
                                   in self._slack_rows(orbit)
                                   if l >= sos_off for p in [rr - row0]]
            for c in self.anchor_lambda:
                pv = c["pv"]
                for (p, l, i, j, v) in sos_side[c["orbit"]]:
                    put(c["row"], l, i, j, pv[p] * v)
        for c in self.anchor_kernel:
            k = c["k"]
            mk = qm.F_sizes[k]
            l = (self.f_off if c["block"] == "F" else self.g_off) + k
            for a in range(mk):
                for b in range(a, mk):
                    put(c["row"], l, a + 1, b + 1, self.Nk[k][a][b])
        return [(k, l, i, j, v) for (k, l, i, j), v in acc.items()]

    def build_entries(self):
        """原始行号（base＋锚定；drop 前）——依赖分析与行泛函自检用。"""
        if self._entries_cache is None:
            base = super().build_entries()
            self._entries_cache = base + self._anchor_entries()
        return self._entries_cache

    def b_vector(self):
        b = super().b_vector()          # 长度已含锚定行（self.m 在 __init__ 更新）
        for r in range(self.m - self.n_anchor_rows + 1, self.m + 1):
            assert b[r - 1] == 0, f"锚定行 {r} 的 b 非零"
        return b

    # ---- 行删除（被依赖蕴含的 base slack 行）＋重编号 ----
    def apply_drop_rows(self, drop_rows):
        """删除 base slack 行并整体重编号（R8-2 工程必需：锚定行与 base 行存在
        精确线性依赖 ⟹ SDPA-GMP 初始 bMat Cholesky 奇异崩溃 cholesky miss/
        not positive definite）。

        等价性论证（双层）：①依赖为有理矩阵零空间（浮点谱证据＋结构性来源：
        AAB/ABC λ 侧列张成亏格），删被蕴含行可行集不变；②即使依赖非精确，
        回读 R1＝λ′−SOS 逐轨道全 monomial L1（含被删行的恒等式行）≤1e-12 的
        接受条款会把任何违例检出——自验证设计，不依赖 ① 的精确性。"""
        assert not self._dropped, "drop 只能应用一次"
        drop = sorted(set(int(r) for r in drop_rows))
        assert all(1 <= r <= 3 * self.qm.nmon for r in drop), \
            f"只允许删 base slack 行（1..{3 * self.qm.nmon}），norm/锚定行不可删：{drop}"
        assert len(drop) <= 3 * self.qm.nmon
        dropset = set(drop)
        rm, shift = {}, 0
        for r in range(1, self.m + 1):
            if r in dropset:
                shift += 1
                rm[r] = None
            else:
                rm[r] = r - shift
        self._dropped = drop
        self.rowmap = rm
        self.m_exported = self.m - len(drop)
        for c in self.anchor_lambda + self.anchor_kernel:
            c["row_exported"] = rm[c["row"]]

    def exported_entries(self):
        """实际写入 .dat-s 的条目（drop 后重编号；k=0 目标行不变）。"""
        if not self._dropped:
            return self.build_entries()
        rm = self.rowmap
        return [(0 if k == 0 else rm[k], l, i, j, v)
                for (k, l, i, j, v) in self.build_entries() if k == 0 or rm[k] is not None]

    def exported_b(self):
        b = self.b_vector()
        if not self._dropped:
            return b
        rm = self.rowmap
        out = [F0] * self.m_exported
        for r in range(1, self.m + 1):
            if rm[r] is not None and b[r - 1]:
                out[rm[r] - 1] = b[r - 1]
        return out

    def write_dat(self, path: Path):
        E = self.exported_entries()
        b = self.exported_b()
        m_dim = self.m_exported if self._dropped else self.m
        with open(path, "w") as f:
            f.write('"N=9 typed (3,3,3) S3-quotient Hermite-fixed + moment-container '
                    'ANCHORED cap SDP (exact rational)"\n')
            f.write(f"{m_dim} = mDIM\n{len(self.blk)} = nBLOCK\n")
            f.write(" ".join(str(s) for s in self.blk) + " = bLOCKsTRUCT\n")
            f.write(" ".join(frac_dec(x) for x in b) + "\n")
            for (k, l, i, j, v) in E:
                f.write(f"{k} {l} {i} {j} {frac_dec(v)}\n")
        return m_dim, len(E)

    def anchor_summary(self) -> dict:
        return dict(groups=list(self.anchor_groups),
                    containers=self.containers_flag,
                    n_anchor_rows=self.n_anchor_rows,
                    n_anchor_constraints=self.n_anchor_constraints,
                    n_lambda_logical=self.anchor_lambda_logical,
                    n_lambda_distinct=len(self.anchor_lambda),
                    lambda_collapse=[dict(orbit=c["orbit"], cls=list(c["cls"]),
                                          uvw=[str(x) for x in c["uvw"]],
                                          mult=len(c["triples"]),
                                          triples=[list(x) for x in c["triples"]])
                                     for c in self.anchor_lambda],
                    n_kernel_rows=len(self.anchor_kernel),
                    dropped_base_rows=list(self._dropped),
                    m_exported=(self.m_exported if self._dropped else self.m))


def _row_gram_nullspace(entries, n_rows, rel_tol=1e-12):
    """约束行 Gram 矩阵 G = A·Aᵀ 的数值零空间（行线性依赖组）。"""
    import numpy as np
    import scipy.sparse as sp
    rows = sorted({k for (k, _l, _i, _j, _v) in entries if k != 0})
    ridx = {r: ii for ii, r in enumerate(rows)}
    pos = {}
    for (_k, l, i, j, _v) in entries:
        if _k == 0:
            continue
        key = (l, min(i, j), max(i, j))
        if key not in pos:
            pos[key] = len(pos)
    ri = [ridx[k] for (k, _l, _i, _j, _v) in entries if k != 0]
    ci = [pos[(l, min(i, j), max(i, j))] for (k, l, i, j, _v) in entries if k != 0]
    dv = [float(v) for (k, _l, _i, _j, v) in entries if k != 0]
    A = sp.csr_matrix((dv, (ri, ci)), shape=(len(rows), len(pos)))
    G = (A @ A.T).toarray()
    G = (G + G.T) / 2
    w, V = np.linalg.eigh(G)
    thr = max(abs(w)) * rel_tol
    nullity = int((w <= thr).sum())
    info = dict(n_rows=len(rows), gram_min_eigs=[float(x) for x in w[:max(nullity + 2, 6)]],
                eig_threshold=float(thr), nullity=nullity,
                smallest_nonzero=(float(w[nullity]) if nullity < len(w) else None))
    return rows, V[:, :nullity], info


def choose_drop_rows(ex: AnchoredCapExporter, rel_tol=1e-12):
    """锚定行接入后的行依赖分析＋极小 drop 集选择（base slack 行内，行主元 QR）。

    机制（(6,6) 段测实证）：锚定 λ 行（纯 SOS 侧模式）与 AAB/ABC base 行存在
    精确线性依赖（有理矩阵零空间）⟹ SDPA-GMP 初始 bMat Cholesky 崩溃。删除被
    依赖蕴含的 base slack 行（可行集不变；见 apply_drop_rows 的双层等价论证）。"""
    import numpy as np
    from scipy.linalg import qr
    rows, N, info = _row_gram_nullspace(ex.build_entries(), ex.m, rel_tol=rel_tol)
    qm = ex.qm
    if info["nullity"] == 0:
        return [], info
    ridx = {r: ii for ii, r in enumerate(rows)}
    base_rows = [r for r in rows if 1 <= r <= 3 * qm.nmon]
    Nsub = N[[ridx[r] for r in base_rows], :]
    _Q, R, piv = qr(Nsub.T, pivoting=True)
    rk = int((np.abs(np.diag(R)) > 1e-9 * max(abs(np.diag(R)))).sum())
    if rk < info["nullity"]:
        fail(f"行依赖无法仅由 base slack 行击中（秩 {rk}/{info['nullity']}）——"
             f"需人工分析（anchored rows 参与依赖的不可删部分）")
    drop = sorted(base_rows[piv[i]] for i in range(info["nullity"]))
    return drop, info


def verify_rows_nonsingular(ex: AnchoredCapExporter, rel_tol=1e-12) -> dict:
    """drop 后复核：导出条目行 Gram 零空间必须为空（数值口径）。"""
    _rows, _N, info = _row_gram_nullspace(ex.exported_entries(),
                                          ex.m_exported, rel_tol=rel_tol)
    if info["nullity"] != 0:
        fail(f"drop 后行 Gram 仍奇异（nullity={info['nullity']}）：{info}")
    return info


def solution_from_parse_anchor(ex: AnchoredCapExporter, parsed: dict, h_AA, h_AB):
    """锚定版回读（containers=False 时无 G 块，G 置零块保持 data 形状）。"""
    if ex.containers_flag:
        return solution_from_parse_moment(ex, parsed, h_AA, h_AA)
    data = _hl_sol_from_parse(ex, parsed, h_AA, h_AA)
    data["G"] = [[[F0] * mk for _ in range(mk)] for mk in ex.mm.sizes]
    return data


def export_row_check_anchor(qm: QuotientMaps, mm: MomentMaps, ex: AnchoredCapExporter,
                            rng) -> dict:
    """锚定行随机泛函逐行核对（selftest ④ 口径）：lambda 行泛函 == −Σ_p pv[p]·
    sos_o[p]（sos_sum 独立装配）＋交叉核对（＋Σ_p pv[p]·(λ′−SOS)[p] ＝ Σ_p
    pv[p]·λ′[p]，即锚定行语义＝λ′(x_T)=0）；kernel 行 == ⟨Ñ,F⟩/⟨Ñ,G⟩ 独立直算。"""
    from hermite_ladder import _row_functional
    d_H1 = qm.d_H + 1
    psi_AA = [Fraction(rng.randint(-9, 9), 7) for _ in range(d_H1)]
    psi_AB = [Fraction(rng.randint(-9, 9), 7) for _ in range(d_H1)]
    cvals = {n: Fraction(rng.randint(-9, 9), 7) for n in ("c_A", "c_B", "c_C")}
    lp_vals = {ex.e_pos: Fraction(25, 1)}
    for name, vec in (("psi_AA", psi_AA), ("psi_AB", psi_AB)):
        pp, mmn = ex.vpos[name]
        for d in range(d_H1):
            lp_vals[pp + d] = vec[d]
            lp_vals[mmn + d] = F0
    for name in cvals:
        pp, mmn = ex.vpos[name]
        lp_vals[pp] = cvals[name]
        lp_vals[mmn] = F0
    mat_vals, F_list, G_list = {}, [], []
    for kk, mk in enumerate(qm.F_sizes):
        Gm = [[Fraction(rng.randint(-6, 6), 4) for _ in range(mk)] for _ in range(mk)]
        Fk = [[sum(Gm[i][t] * Gm[j][t] for t in range(mk)) for j in range(mk)]
              for i in range(mk)]
        F_list.append(Fk)
        mat_vals[ex.f_off + kk] = Fk
    for kk, mk in enumerate(mm.sizes):
        Gm = [[Fraction(rng.randint(-6, 6), 4) for _ in range(mk)] for _ in range(mk)]
        Gk = [[sum(Gm[i][t] * Gm[j][t] for t in range(mk)) for j in range(mk)]
              for i in range(mk)]
        G_list.append(Gk)
        if ex.containers_flag:
            mat_vals[ex.g_off + kk] = Gk
    B = {}
    for oi, orbit in enumerate(("AAA", "AAB", "ABC")):
        for bi, (name, _g, mons) in enumerate(qm.sos_def):
            m_ = len(mons)
            Gm = [[Fraction(rng.randint(-6, 6), 4) for _ in range(m_)] for _ in range(m_)]
            Bm = [[sum(Gm[i][t] * Gm[j][t] for t in range(m_)) for j in range(m_)]
                  for i in range(m_)]
            B[f"{orbit}_{name}"] = Bm
            mat_vals[ex.sos_off + oi * len(qm.sos_def) + bi] = Bm
    func = _row_functional(ex.build_entries(), lp_vals, mat_vals)
    b = ex.b_vector()
    data = dict(h_AA=ex.h_AA, h_AB=ex.h_AB, psi_AA=psi_AA, psi_AB=psi_AB,
                c_A=cvals["c_A"], c_B=cvals["c_B"], c_C=cvals["c_C"],
                e=lp_vals[ex.e_pos], F=F_list, G=G_list, B=B)
    n_chk = 0
    for c in ex.anchor_lambda:
        orbit = c["orbit"]
        pv = c["pv"]
        sv = qm.sos_sum({nm: B[f"{orbit}_{nm}"] for (nm, _g, _m) in qm.sos_def})
        lv = (moment_lam(qm, mm, orbit, data) if ex.containers_flag
              else qm.lam(orbit, data))
        lhs = func.get(c["row"], F0) - b[c["row"] - 1]
        sos_eval = sum(pv[p] * sv[p] for p in range(qm.nmon))
        if lhs != -sos_eval:
            fail(f"锚定 lambda 行泛函不一致（{orbit} {c['uvw']}）：{lhs} ≠ {-sos_eval}")
        # 交叉核对：base 行语义 pv·(λ′−SOS) − 锚定行 == pv·λ′（锚定＝λ′(x_T)=0）
        base_pv = F0
        row0 = ex.orbit_row[orbit]
        for p in range(qm.nmon):
            base_pv += pv[p] * (func.get(row0 + p, F0) - b[row0 + p - 1])
        if base_pv - lhs != sum(pv[p] * lv[p] for p in range(qm.nmon)):
            fail(f"锚定 lambda 行交叉核对不一致（{orbit} {c['uvw']}）")
        n_chk += 1
    for c in ex.anchor_kernel:
        k = c["k"]
        mat = (F_list if c["block"] == "F" else G_list)[k]
        Nk_ = ex.Nk[k]
        expect = sum(Nk_[a][a] * mat[a][a] for a in range(len(mat))) \
            + 2 * sum(Nk_[a][b] * mat[a][b] for a in range(len(mat))
                      for b in range(a + 1, len(mat)))
        lhs = func.get(c["row"], F0) - b[c["row"] - 1]
        if lhs != expect:
            fail(f"锚定 kernel 行泛函不一致（{c['block']}{k}）：{lhs} ≠ {expect}")
        n_chk += 1
    return dict(rows_checked=n_chk, ok=True)


def anchored_readback(qm: QuotientMaps, mm: MomentMaps, ex: AnchoredCapExporter,
                      data: dict, Gram_ttp) -> dict:
    """锚定解的全套精确回读（幂等单一事实源；求解器与验收门共用）：
    R1（λ′−SOS 逐轨道 L1）、归一化残差、锚定残差（84 逻辑 λ′(x_T) 逐行展开、
    kernel ⟨F/G,Ñ_k⟩）、恒等式 (∗) 在锚定 Gram 的回读残差、E_anchor、
    dist（E_ttp 全精度为主、9 位并列）。全部 exact Fraction，float 仅为显示。"""
    ring = qm.ring
    R1 = {}
    lam_orbit = {}
    for orbit in ("AAA", "AAB", "ABC"):
        lv = (moment_lam(qm, mm, orbit, data) if ex.containers_flag
              else qm.lam(orbit, data))
        lam_orbit[orbit] = lv
        sv = qm.sos_sum({nm: data["B"][f"{orbit}_{nm}"] for (nm, _g, _m) in qm.sos_def})
        R1[orbit] = sum(abs(x - y) for x, y in zip(lv, sv))
    nrm_resid = (qm.nrm["c_A"] * data["c_A"] + qm.nrm["c_B"] * data["c_B"]
                 + qm.nrm["c_C"] * data["c_C"] + qm.nrm["e"] * data["e"]
                 - Fraction(qm.s111_factor) * sum(sum(r) for r in data["F"][0]))
    # 锚定 λ 残差（逻辑 84：合并行值 × 重数展开——同一行值对每个同 (u,v,t) 三元组相同）
    lam_rows = []
    for c in ex.anchor_lambda:
        val = sum(c["pv"][p] * lam_orbit[c["orbit"]][p] for p in range(qm.nmon))
        lam_rows.append(dict(row=c["row"], orbit=c["orbit"],
                             cls="".join(str(x) for x in c["cls"]),
                             mult=len(c["triples"]), val=val,
                             absmax=abs(val) * len(c["triples"])))
    lam_resid_logical = sum(r["absmax"] for r in lam_rows)      # Σ_T |λ′(x_T)|（保守）
    lam_resid_maxrow = max((abs(r["val"]) for r in lam_rows), default=F0)
    kernel_rows = []
    for c in ex.anchor_kernel:
        k = c["k"]
        mat = (data["F"] if c["block"] == "F" else data["G"])[k]
        Nk_ = ex.Nk[k]
        val = sum(Nk_[a][b] * mat[a][b] for a in range(len(mat))
                  for b in range(len(mat)))
        kernel_rows.append(dict(row=c["row"], block=c["block"], k=k, val=val))
    kernel_absmax = max((abs(r["val"]) for r in kernel_rows), default=F0)
    # 恒等式 (∗) 回读（锚定 Gram，全 exact 直算）
    s_vec, _ = qm.s_forms(data)
    sum_all = F0
    for i in range(N):
        for j in range(N):
            for l in range(N):
                sum_all += ring.eval3(s_vec, Gram_ttp[i][j], Gram_ttp[i][l],
                                      Gram_ttp[j][l])
    sum_lam = sum(r["val"] * r["mult"] for r in lam_rows) \
        if ex.anchor_lambda else None
    if sum_lam is None:      # 无 lambda 组（不应发生；防呆走全 84 直算）
        sum_lam = F0
    sum_cont = F0
    for k in range(qm.K):
        Gk, Mk = data["G"][k], ex.Nk[k]
        for a in range(len(Gk)):
            for b in range(len(Gk)):
                if Gk[a][b]:
                    sum_cont += Gk[a][b] * Mk[a][b]
    E_anchor = anchor_sum_H(Gram_ttp)
    sum_H = E_anchor          # h_AA=h_AB=同一 minorant ⟹ ΣH 与 M 无关
    identity_resid = (sum_lam + sum_all + sum_cont) - (sum_H - data["e"])
    e_v = data["e"]
    return dict(R1=R1, nrm=nrm_resid, lam_rows=lam_rows, kernel_rows=kernel_rows,
                lam_resid_maxrow=lam_resid_maxrow,
                lam_resid_logical_sum=lam_resid_logical,
                kernel_absmax=kernel_absmax, sum_all=sum_all, sum_cont=sum_cont,
                identity_resid=identity_resid, E_anchor=E_anchor,
                e=e_v, dist_full=E_TTP_TUBE - e_v, dist_9dp=E_STAR_9DP - e_v)


def solve_anchored_cap(a0: Fraction, M: int, K: int, sdpa_bin: Path, arm: str,
                       groups=("lambda", "kernel"), containers=True, k_minor: int = 48,
                       timeout_s=43200):
    """锚定 cap SDP 求解（SDPA-GMP；R8-2）。接受条款同 hermite_ladder：pdOPT，
    或停滞点（R1≤1e-12 且锚定残差逐项 ≤1e-9，如实标注 stalled_point）。"""
    tag = rung_tag(a0)
    dy = minorant_for(M, k_minor)
    assert M >= 7, "锚定探针需 d_H≥11（6 节点 minorant），M≥7"
    qm = QuotientMaps(a0, M, K)
    mm = MomentMaps(qm)
    h_AA = pad_h(dy["coeffs"], qm.d_H)
    Gram_ttp, z_mid = ttp_anchor_gram()
    ex = AnchoredCapExporter(qm, mm, h_AA, h_AA, Gram_ttp, groups=groups,
                             containers=containers)
    rc = export_row_check_anchor(qm, mm, ex, random.Random(SEED_ANCHOR + M))
    print(f"[anchor-check] {arm} 预检（drop 前全量行泛函）：{rc}", flush=True)
    try:
        import numpy                                                    # noqa: F401
        import scipy                                                    # noqa: F401
    except ImportError:
        fail("锚定求解需要 numpy/scipy 做行依赖分析——请用 numerics/.venv/bin/python 运行")
    drops, dep_info = choose_drop_rows(ex)
    if drops:
        ex.apply_drop_rows(drops)
        dep_info["post_check"] = verify_rows_nonsingular(ex)
        print(f"[anchor-drop] 删除被依赖蕴含的 base slack 行 {drops}"
              f"（nullity {dep_info['nullity']}→0 复核过）", flush=True)
    else:
        print("[anchor-drop] 无行依赖（nullity=0），不删行", flush=True)
    arm_tag = f"{tag}_M{M}_{arm}" + ("" if containers else "_baseline")
    workdir = HERE / "results" / "anchor_work" / f"cap_{arm_tag}"
    workdir.mkdir(parents=True, exist_ok=True)
    dat = workdir / "anchor_cap.dat-s"
    if dat.exists():
        dat.unlink()
    t0 = time.time()
    m_dim, n_entries = ex.write_dat(dat)
    export_s = time.time() - t0
    (workdir / "param.sdpa").write_text(PARAM_SDPA_TUNED)
    result = workdir / "anchor_cap.result"
    sol_path = HERE / "results" / f"anchor_sol_{arm_tag}.json"
    summary = ex.anchor_summary()
    print(f"[anchor-export] {arm_tag}: m={m_dim}, entries={n_entries}, "
          f"blocks={len(ex.blk)}（锚定行 {summary['n_anchor_rows']}＝"
          f"lambda {summary['n_lambda_logical']}→{summary['n_lambda_distinct']} 合并"
          f"＋kernel {summary['n_kernel_rows']}），导出 {export_s:.0f}s", flush=True)
    cmd = [str(sdpa_bin), "-ds", str(dat), "-o", str(result),
           "-p", str(workdir / "param.sdpa")]

    def readback(parsed):
        data_ = solution_from_parse_anchor(ex, parsed, h_AA, h_AA)
        rb = anchored_readback(qm, mm, ex, data_, Gram_ttp)
        return data_, rb

    def accept(parsed_cand):
        if parsed_cand["info"]["phase_value"] == "pdOPT":
            return True, False
        try:
            _d, rb_c = readback(parsed_cand)
            ok = (max(rb_c["R1"].values()) <= STALLED_R1_TOL
                  and rb_c["lam_resid_maxrow"] <= Fraction(1, 10 ** 9)
                  and rb_c["kernel_absmax"] <= Fraction(1, 10 ** 9))
            return ok, ok
        except SystemExit:
            return False, False

    reused, parsed, stalled = False, None, False
    if result.exists():
        try:
            cand = parse_result(result)
            ok, st = accept(cand)
            if ok:
                reused, parsed, stalled = True, cand, st
        except SystemExit:
            pass
    if reused:
        info = parsed["info"]
        print(f"[anchor-solve] {arm_tag}: 复用已有结果（phase={info['phase_value']}）",
              flush=True)
        solve_s = 0.0
    else:
        if result.exists():
            result.unlink()
        print(f"[anchor-solve] {arm_tag}: {' '.join(cmd)}", flush=True)
        t0 = time.time()
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              cwd=str(workdir), timeout=timeout_s)
        solve_s = time.time() - t0
        if proc.returncode != 0 or not result.exists():
            fail(f"anchor cap {arm_tag}: sdpa_gmp 退出码 {proc.returncode}："
                 f"{proc.stdout[-1500:]} {proc.stderr[-1500:]}")
        parsed = parse_result(result)
        ok, stalled = accept(parsed)
        if not ok:
            # 未达接受条款：如实记停滞/不可行原始信息（诊断口径），不 crash——
            # 探针两分支都是决定性信息（D19 裁决 3）
            print(f"[anchor-solve] {arm_tag}: 未达接受条款（phase="
                  f"{parsed['info']['phase_value']}）——按原始停滞点入档诊断",
                  flush=True)
            stalled = False
        info = parsed["info"]
    print(f"[anchor-solve] {arm_tag}: phase={info['phase_value']} iter={info['iteration']} "
          f"mu={info['mu']:.2e} relgap={info['relative_gap']:.2e} ({solve_s:.0f}s)", flush=True)
    data = solution_from_parse_anchor(ex, parsed, h_AA, h_AA)
    rb = anchored_readback(qm, mm, ex, data, Gram_ttp)
    accepted = (info["phase_value"] == "pdOPT") or stalled
    hygiene = dict(
        e_le_E_ttp_1e_9=bool(data["e"] <= E_TTP_TUBE + Fraction(1, 10 ** 9)),
        R1_le_1e_12=bool(max(rb["R1"].values()) <= STALLED_R1_TOL),
        anchor_lambda_le_1e_9=bool(rb["lam_resid_maxrow"] <= Fraction(1, 10 ** 9)),
        anchor_kernel_le_1e_9=bool(rb["kernel_absmax"] <= Fraction(1, 10 ** 9)),
        identity_le_1e_12=bool(abs(rb["identity_resid"]) <= Fraction(1, 10 ** 12)),
    )
    hygiene["all_ok"] = all(hygiene.values())
    if accepted and not hygiene["all_ok"]:
        # pdOPT/停滞点解仍违反卫生断言 ⇒ 装配或求解事故（硬失败，不静默）
        fail(f"anchor cap {arm_tag}: 已接受解违反卫生断言 {hygiene}（e="
             f"{float(data['e']):.15f}）")
    print(f"[anchor-resid] {arm_tag}: e = {float(data['e']):.15f}；R1_max = "
          f"{float(max(rb['R1'].values())):.2e}；λ′行最大 = "
          f"{float(rb['lam_resid_maxrow']):.2e}；kernel 最大 = "
          f"{float(rb['kernel_absmax']):.2e}；(∗) 回读 = "
          f"{float(rb['identity_resid']):.2e}；dist(E_ttp) = "
          f"{float(rb['dist_full']):.3e}", flush=True)
    sol_js = dict(
        kind="n9-anchor-probe-solution", arm=arm, tag=arm_tag,
        a0=str(a0), M=M, K=K, groups=list(groups), containers=bool(containers),
        minorant_k=k_minor,
        dependency=dep_info,
        anchor=dict(round_decimals=ANCHOR_ROUND_DECIMALS, z_mid=z_mid,
                    zStarInterval=list(Z_STAR_INTERVAL),
                    Gram=[[str(x) for x in row] for row in Gram_ttp],
                    E_anchor=str(rb["E_anchor"]),
                    E_ttp_full=str(E_TTP_TUBE), E_star_9dp=str(E_STAR_9DP)),
        e=float(data["e"]),
        exact=dict(h_AA=[str(x) for x in data["h_AA"]],
                   h_AB=[str(x) for x in data["h_AB"]],
                   psi_AA=[str(x) for x in data["psi_AA"]],
                   psi_AB=[str(x) for x in data["psi_AB"]],
                   c_A=str(data["c_A"]), c_B=str(data["c_B"]), c_C=str(data["c_C"]),
                   e=str(data["e"]),
                   F=[[[str(x) for x in row] for row in m_] for m_ in data["F"]],
                   G=[[[str(x) for x in row] for row in m_] for m_ in data["G"]],
                   B={n: [[str(x) for x in row] for row in m_]
                      for n, m_ in data["B"].items()},
                   note="SDPA-GMP .result 66 位十进制精确回读的 Fraction"),
        solver=dict(route="SDPA-GMP 7.1.3 (GMP 200) + anchored rows",
                    reused=bool(reused), stalled_point=bool(stalled),
                    accepted=bool(accepted), solve_s=round(solve_s, 1),
                    export_s=round(export_s, 1),
                    lp_penalty=str(ex.lp_penalty),
                    param="betaStar0.05/betaBar0.15/eps1e-25/maxIter2000",
                    m=m_dim, entries=n_entries, blocks=len(ex.blk),
                    **info),
        anchor_rows=summary,
        readback=dict(
            R1={o: str(v) for o, v in rb["R1"].items()},
            nrm=str(rb["nrm"]),
            lam_resid_maxrow=str(rb["lam_resid_maxrow"]),
            lam_resid_logical_sum=str(rb["lam_resid_logical_sum"]),
            kernel_absmax=str(rb["kernel_absmax"]),
            lam_rows=[dict(row=r["row"], orbit=r["orbit"], cls=r["cls"],
                           mult=r["mult"], val=str(r["val"])) for r in rb["lam_rows"]],
            kernel_rows=[dict(row=r["row"], block=r["block"], k=r["k"],
                              val=str(r["val"])) for r in rb["kernel_rows"]],
            sum_all=str(rb["sum_all"]), sum_cont=str(rb["sum_cont"]),
            identity_resid=str(rb["identity_resid"]),
            E_anchor=str(rb["E_anchor"]), e=str(rb["e"]),
            dist_full=str(rb["dist_full"]), dist_9dp=str(rb["dist_9dp"])),
        hygiene={k2: bool(v) for k2, v in hygiene.items()},
        code_version=code_version(),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
    )
    sol_path.write_text(json.dumps(sol_js, ensure_ascii=False))
    print(f"[anchor-out] {arm_tag}: 解数据 {sol_path.relative_to(REPO)}", flush=True)
    return sol_path, dict(accepted=accepted, sdpa_info=info,
                          solve_s=round(solve_s, 1), export_s=round(export_s, 1),
                          m=m_dim, entries=n_entries)


ANCHOR_ARM_SPECS = {
    "A": dict(M=7, K=6, containers=True, groups=("lambda", "kernel")),
    "B": dict(M=9, K=6, containers=True, groups=("lambda", "kernel")),
    "C": dict(M=9, K=6, containers=False, groups=("lambda", "kernel")),
}
ANCHOR_ARCHIVE = "anchor_probe_m9.json"


def assert_arm_legality(e_fraction: Fraction) -> None:
    """卫生断言靶函数（R8-2 验收门负对照 (b) 的靶）：e ≤ E_ttp + 1e-9。

    锚定可行点恒有 e = E_anchor < E_ttp（identity (∗) 在锚定 Gram 精确）；
    违者＝装配或求解事故（求解路径对 accepted 解硬失败，此处独立可调用）。"""
    if not (e_fraction <= E_TTP_TUBE + Fraction(1, 10 ** 9)):
        print(f"[legality] FAIL: e = {float(e_fraction):.15f} > E_ttp + 1e-9"
              f"（E_ttp = {float(E_TTP_TUBE):.15f}）", flush=True)
        sys.exit(1)
    print(f"[legality] ok: e = {float(e_fraction):.15f} ≤ E_ttp + 1e-9", flush=True)


def recompute_anchor_arm(sol_path: Path) -> dict:
    """从存档 sol 重算全套回读（幂等单一事实源；--anchor-finalize 与 r8 门共用）。

    不触求解、不重建导出条目（AnchoredCapExporter 只走锚定行构造路径）。"""
    sol = json.loads(sol_path.read_text())
    a0 = Fraction(sol["a0"])
    M, K = sol["M"], sol["K"]
    qm = QuotientMaps(a0, M, K)
    mm = MomentMaps(qm)
    dy = minorant_for(M, sol["minorant_k"])
    h_AA = pad_h(dy["coeffs"], qm.d_H)
    Gram = [[Fraction(x) for x in row] for row in sol["anchor"]["Gram"]]
    ex = AnchoredCapExporter(qm, mm, h_AA, h_AA, Gram,
                             groups=tuple(sol["groups"]),
                             containers=sol["containers"])
    e_ = sol["exact"]
    data = dict(h_AA=list(h_AA), h_AB=list(h_AA),
                psi_AA=[Fraction(x) for x in e_["psi_AA"]],
                psi_AB=[Fraction(x) for x in e_["psi_AB"]],
                c_A=Fraction(e_["c_A"]), c_B=Fraction(e_["c_B"]),
                c_C=Fraction(e_["c_C"]), e=Fraction(e_["e"]),
                F=[[[Fraction(x) for x in row] for row in m_] for m_ in e_["F"]],
                G=[[[Fraction(x) for x in row] for row in m_] for m_ in e_["G"]],
                B={k2: [[Fraction(x) for x in row] for row in m_]
                   for k2, m_ in e_["B"].items()})
    rb = anchored_readback(qm, mm, ex, data, Gram)
    rb_js = dict(
        R1={o: str(v) for o, v in rb["R1"].items()},
        nrm=str(rb["nrm"]),
        lam_resid_maxrow=str(rb["lam_resid_maxrow"]),
        lam_resid_logical_sum=str(rb["lam_resid_logical_sum"]),
        kernel_absmax=str(rb["kernel_absmax"]),
        lam_rows=[dict(row=r["row"], orbit=r["orbit"], cls=r["cls"],
                       mult=r["mult"], val=str(r["val"])) for r in rb["lam_rows"]],
        kernel_rows=[dict(row=r["row"], block=r["block"], k=r["k"],
                          val=str(r["val"])) for r in rb["kernel_rows"]],
        sum_all=str(rb["sum_all"]), sum_cont=str(rb["sum_cont"]),
        identity_resid=str(rb["identity_resid"]),
        E_anchor=str(rb["E_anchor"]), e=str(rb["e"]),
        dist_full=str(rb["dist_full"]), dist_9dp=str(rb["dist_9dp"]))
    assert rb_js == sol["readback"], \
        f"{sol_path.name}: 幂等重算与存档 readback 不一致（装配/存档被篡改？）"
    hygiene = dict(
        e_le_E_ttp_1e_9=bool(data["e"] <= E_TTP_TUBE + Fraction(1, 10 ** 9)),
        R1_le_1e_12=bool(max(rb["R1"].values()) <= STALLED_R1_TOL),
        anchor_lambda_le_1e_9=bool(rb["lam_resid_maxrow"] <= Fraction(1, 10 ** 9)),
        anchor_kernel_le_1e_9=bool(rb["kernel_absmax"] <= Fraction(1, 10 ** 9)),
        identity_le_1e_12=bool(abs(rb["identity_resid"]) <= Fraction(1, 10 ** 12)))
    hygiene["all_ok"] = all(hygiene.values())
    assert hygiene == sol["hygiene"], f"{sol_path.name}: 幂等重算 hygiene 不一致"
    return dict(sol=sol, data=data, rb=rb, hygiene=hygiene, sol_path=sol_path)


def anchor_arm_record(arm: str, rec: dict, cmdline: str) -> dict:
    """单臂账本记录（判据字段与数据严格对应；dist/verdict 单一来源 anchored_readback）。"""
    sol, rb, hyg = rec["sol"], rec["rb"], rec["hygiene"]
    info = sol["solver"]
    return dict(
        arm=arm, M=sol["M"], K=sol["K"], a0=sol["a0"], groups=sol["groups"],
        containers=sol["containers"], minorant_k=sol["minorant_k"],
        sol=str(rec["sol_path"].relative_to(REPO)),
        solver=dict(phase=info.get("phase_value"), iteration=info.get("iteration"),
                    mu=info.get("mu"), relative_gap=info.get("relative_gap"),
                    solve_s=info.get("solve_s"), export_s=info.get("export_s"),
                    reused=info.get("reused"), stalled_point=info.get("stalled_point"),
                    route=info.get("route"), m=info.get("m"), entries=info.get("entries")),
        accepted=info.get("accepted"),
        e_val=float(Fraction(sol["exact"]["e"])),
        e_exact=sol["exact"]["e"],
        dist_full=float(rb["dist_full"]), dist_9dp=float(rb["dist_9dp"]),
        E_anchor=str(rb["E_anchor"]),
        R1={o: float(v) for o, v in rb["R1"].items()},
        nrm_resid=float(rb["nrm"]),
        anchor_lambda_maxrow=float(rb["lam_resid_maxrow"]),
        anchor_lambda_logical_sum=float(rb["lam_resid_logical_sum"]),
        anchor_kernel_max=float(rb["kernel_absmax"]),
        identity_readback=float(rb["identity_resid"]),
        hygiene=hyg,
        anchor_rows=sol["anchor_rows"],
        readback_exact=sol["readback"],
        cmdline=cmdline, code_version=sol["code_version"],
        timestamp=sol["timestamp"])


def anchor_verdict(records: dict, arm_cmds: dict = None) -> dict:
    """判死活（D13 裁决 2 判据沿用；D19 裁决 3 口径）。

    alive ⇔ Arm B（(9,6) 全组＋容器）被接受（pdOPT 或停滞点条款）且
    dist = E_ttp − e_val ≤ 1e-6（E_ttp 全精度口径为主，9 位 E* 并列一致判定）。
    否则 dead-at-(9,6)：M-scaling 比（A vs B dist）与按阶梯斜率外推的 M* 区间
    两分支均为第 4 轮定向的决定性信息。"""
    arm_cmds = arm_cmds or {}
    arms = {a: anchor_arm_record(a, r, arm_cmds.get(a, f"--anchor-cap {a}"))
            for a, r in records.items()}
    A, B = arms.get("A"), arms.get("B")
    if B is None or A is None:
        return dict(verdict="incomplete", arms=arms, rule="需 Arm A 与 Arm B 均在档")
    b_alive = bool(B["accepted"]) and B["dist_full"] <= 1e-6 \
        and B["dist_9dp"] <= 1e-6 and B["hygiene"]["all_ok"]
    dA, dB = A["dist_full"], B["dist_full"]
    phA = (A["solver"] or {}).get("phase")
    phB = (B["solver"] or {}).get("phase")
    feas_note = {a: ("pdINF＝求解器判锚定系统不可行（e_val 为不可行证书点读回，"
                     "非锚定最优值；R1 大为其特征）" if (arms[a]["solver"] or {}).get("phase") == "pdINF"
                 else "") for a in arms}
    m_scaling = dict(dist_A=dA, dist_B=dB,
                     ratio=(dA / dB if dA > 0 and dB > 0 else None),
                     phase_A=phA, phase_B=phB, dist_semantics=feas_note,
                     note="dist_A/dist_B（M 7→9 两档）；dist 仅对 accepted 臂有锚定语义")
    rho = math.sqrt(dA / dB) if (dA > 0 and dB > 0) else None
    m_star = None
    if not b_alive:
        if phA == "pdINF" and phB == "pdINF":
            m_star = dict(note=("两档均 pdINF：锚定系统在 (7,6) 与 (9,6) 均不可行——"
                                "不可行是结构性的（KLT 等号条件与 λ-SOS 松弛冲突），"
                                "非档位受限；M* 外推不适用（无 dist 序列）"),
                          phase_A=phA, phase_B=phB)
        elif phB == "pdINF":
            m_star = dict(note=("Arm B pdINF：(9,6) 锚定系统不可行（dead 的直接证据："
                                "KLT 命题 4.3 等号证书在该档不可达）；M* 外推不适用"),
                          phase_B=phB)
        elif dB > 1e-6 and rho and rho > 1.0:
            need = dB / 1e-6
            m_obs = 9 + math.log(need) / math.log(rho)
            m_3x = 9 + math.log(need) / math.log(3.0)
            m_star = dict(needed_reduction=need, rho_per_rung_observed=rho,
                          M_star_observed_slope=m_obs, M_star_prior_3x=m_3x,
                          interval=[min(m_obs, m_3x), max(m_obs, m_3x)],
                          floor=("dist 下限＝E_ttp−E_anchor=2.49e-12（锚定 Gram 舍入）；"
                                 "alive 的实质是可行性问题而非 dist 渐缩"))
        elif dB <= 1e-6:
            m_star = dict(note="dist_B ≤1e-6 但未被接受/卫生未过——按未接受口径判死",
                          dB=dB, accepted=B["accepted"], hygiene=B["hygiene"])
        else:
            m_star = dict(note="dist 无改善或发散——M 阶梯外推不可达（斜率 ≤1）",
                          dist_A=dA, dist_B=dB)
    return dict(
        verdict="alive" if b_alive else "dead-at-(9,6)",
        rule=("alive ⇔ Arm B (9,6) 全组+容器被接受（pdOPT 或停滞点 R1≤1e-12 且"
              "锚定残差≤1e-9）且 dist=E_ttp−e_val≤1e-6（全精度为主/9 位并列，"
              "D13 裁决 2 判据）；否则 dead-at-(9,6)。pdINF＝求解器判锚定系统"
              "不可行（dead 分支的机制性证据；证书点 e_val/dist 无最优值语义）。"
              "两分支均为第 4 轮定向的决定性信息（D19 裁决 3）"),
        arm_B_accepted=B["accepted"], arm_B_hygiene=B["hygiene"],
        dist_A=dA, dist_B=dB, m_scaling=m_scaling, M_star=m_star,
        r7_1_scs_baseline=R7_1_SCS_BASELINE,
        arm_A_replaces_r7_1_baseline=("Arm A (7,6) SDPA-GMP 重测替换 R7-1 SCS "
                                      "optimal_inaccurate 基线（旧值入档对照）"),
        arms=arms)


def run_anchor_finalize(out: Path = None, arm_cmds: dict = None):
    """从存档 sol 重算全部臂并写 anchor_probe_m9.json（幂等；门共用同一重算）。"""
    out = out or HERE / "results" / ANCHOR_ARCHIVE
    arm_cmds = arm_cmds or {}
    records = {}
    for arm in ("A", "B", "C"):
        spec = ANCHOR_ARM_SPECS[arm]
        name = (f"anchor_sol_{rung_tag(Fraction(-187, 250))}_M{spec['M']}_{arm}"
                + ("" if spec["containers"] else "_baseline") + ".json")
        p = HERE / "results" / name
        if p.exists():
            records[arm] = recompute_anchor_arm(p)
    if not records:
        fail("无锚定 sol 在档（先跑 --anchor-cap A / B）")
    verdict = anchor_verdict(records, arm_cmds)
    Gram, z_mid = ttp_anchor_gram()
    E_anchor = anchor_sum_H(Gram)
    outd = dict(
        kind="n9-bounds-anchor-probe", schema="thomson-n9/bounds/anchor-probe/1",
        seed=SEED_ANCHOR, code_version=code_version(),
        generated=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        reference=dict(
            E_ttp_full=str(E_TTP_TUBE), E_star_9dp=str(E_STAR_9DP),
            E_ttp_minus_E_anchor=float(E_TTP_TUBE - E_anchor),
            E_anchor=str(E_anchor),
            source="thomson-workflow/data/energies.json（E* 9 位）＋tube.json E_ttp 全精度（hermite_ladder.E_TTP_TUBE）"),
        anchor=dict(
            config="D3h tricapped prism @ z* 区间中点（family.tri_cap_prism 同构，纯 math 重实现）",
            zStarInterval=list(Z_STAR_INTERVAL), z_mid=z_mid,
            round_decimals=ANCHOR_ROUND_DECIMALS,
            identity_exact_at_anchor_gram=("(∗) 在对称 Gram 上精确成立（本会话 precheck "
                                           "随机数据 exact 验证；锚定 Gram 12 位十进有理）"),
            types=list(ANCHOR_TYPES)),
        arms=verdict.pop("arms"),
        verdict=verdict,
        provenance=dict(
            seed=SEED_ANCHOR, code_version=code_version(),
            sdpa_bin=os.environ.get("SDPA_GMP_BIN", "/tmp/hpbuild/sdpa-gmp-7.1.3/sdpa_gmp"),
            commands={a: arm_cmds.get(a, f"python3 numerics/bounds/moment_lift.py "
                                        f"--anchor-cap {a}") for a in records},
            minorant="a5 固定 minorant fixed_minorant(48)（两臂同参；M≥7 全节点）",
            acceptance="pdOPT 或停滞点（R1≤1e-12 且锚定残差逐项≤1e-9，hermite_ladder 条款）"),
    )
    p = Path(out)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(outd, ensure_ascii=False, indent=1) + "\n")
    dA, dB = outd["verdict"].get("dist_A"), outd["verdict"].get("dist_B")
    print(f"[anchor-finalize] verdict = {outd['verdict']['verdict']}；"
          f"dist_A = {dA if dA is None else format(dA, '.3e')}；"
          f"dist_B = {dB if dB is None else format(dB, '.3e')} → "
          f"{p.relative_to(REPO)}", flush=True)
    return outd


def solve_cap_moment(a0: Fraction, M: int, K: int, sdpa_bin: Path, k_minor: int = 48,
                     timeout_s=43200):
    tag = rung_tag(a0)
    dy = minorant_for(M, k_minor)
    qm = QuotientMaps(a0, M, K)
    mm = MomentMaps(qm)
    h_AA = pad_h(dy["coeffs"], qm.d_H)
    ex = MomentCapExporter(qm, mm, h_AA, h_AA)
    workdir = HERE / "results" / "moment_work" / f"cap_{tag}_M{M}"
    workdir.mkdir(parents=True, exist_ok=True)
    dat = workdir / "moment_cap.dat-s"
    if dat.exists():
        dat.unlink()
    m_dim, n_entries = ex.write_dat(dat)
    (workdir / "param.sdpa").write_text(PARAM_SDPA_TUNED)
    result = workdir / "moment_cap.result"
    sol_path = HERE / "results" / f"moment_cap_sol_{tag}_M{M}.json"
    print(f"[export] moment cap {tag} M={M}: m={m_dim}, entries={n_entries}, "
          f"blocks={len(ex.blk)} (n_lp={ex.n_lp})", flush=True)
    cmd = [str(sdpa_bin), "-ds", str(dat), "-o", str(result),
           "-p", str(workdir / "param.sdpa")]

    def accept(parsed_cand):
        if parsed_cand["info"]["phase_value"] == "pdOPT":
            return True, False
        try:
            data_c = solution_from_parse_moment(ex, parsed_cand, h_AA, h_AA)
            rr_c = raw_residuals_moment(qm, mm, data_c)
            ok = max(rr_c["R1"].values()) <= STALLED_R1_TOL
            return ok, ok
        except SystemExit:
            return False, False

    reused, parsed, stalled = False, None, False
    if result.exists():
        try:
            cand = parse_result(result)
            ok, st = accept(cand)
            if ok:
                reused, parsed, stalled = True, cand, st
        except SystemExit:
            pass
    if reused:
        info = parsed["info"]
        print(f"[solve] moment cap {tag}: 复用已有结果（phase={info['phase_value']}）",
              flush=True)
        solve_s = 0.0
    else:
        if result.exists():
            result.unlink()
        print(f"[solve] moment cap {tag}: {' '.join(cmd)}", flush=True)
        t0 = time.time()
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              cwd=str(workdir), timeout=timeout_s)
        solve_s = time.time() - t0
        if proc.returncode != 0 or not result.exists():
            fail(f"moment cap {tag}: sdpa_gmp 退出码 {proc.returncode}："
                 f"{proc.stdout[-1500:]} {proc.stderr[-1500:]}")
        parsed = parse_result(result)
        ok, stalled = accept(parsed)
        if not ok:
            fail(f"moment cap {tag}: SDPA-GMP 未达 pdOPT 且停滞点回读残差超阈："
                 f"{parsed['info']['phase_value']}")
        info = parsed["info"]
    print(f"[solve] moment cap {tag}: phase={info['phase_value']} iter={info['iteration']} "
          f"mu={info['mu']:.2e} relgap={info['relative_gap']:.2e} "
          f"({solve_s:.0f}s)" + ("；**停滞点认证（可能次优）**" if stalled else ""),
          flush=True)
    data = solution_from_parse_moment(ex, parsed, h_AA, h_AA)
    if data["e"] > E_TTP_TUBE + Fraction(1, 10 ** 6):
        fail(f"moment cap {tag}: e = {float(data['e']):.15f} > E_ttp+1e-6（导出有误）")
    rr = raw_residuals_moment(qm, mm, data)
    print(f"[resid] moment cap {tag}: e = {float(data['e']):.15f}；R1 = "
          f"{ {k2: float(v) for k2, v in rr['R1'].items()} }", flush=True)
    sol_js = dict(
        tag=tag, a0=str(a0), M=M, K=K, minorant_k=k_minor,
        e=float(data["e"]),
        exact=dict(h_AA=[str(x) for x in data["h_AA"]],
                   h_AB=[str(x) for x in data["h_AB"]],
                   psi_AA=[str(x) for x in data["psi_AA"]],
                   psi_AB=[str(x) for x in data["psi_AB"]],
                   c_A=str(data["c_A"]), c_B=str(data["c_B"]), c_C=str(data["c_C"]),
                   e=str(data["e"]),
                   F=[[[str(x) for x in row] for row in m_] for m_ in data["F"]],
                   G=[[[str(x) for x in row] for row in m_] for m_ in data["G"]],
                   B={n: [[str(x) for x in row] for row in m_] for n, m_ in data["B"].items()},
                   note="SDPA-GMP .result 66 位十进制精确回读的 Fraction"),
        solver_info=dict(route="SDPA-GMP 7.1.3 (GMP 200) + moment containers",
                         reused=bool(reused), stalled_point=bool(stalled),
                         solve_s=round(solve_s, 1), lp_penalty=str(ex.lp_penalty),
                         param="betaStar0.05/betaBar0.15/eps1e-25/maxIter2000",
                         **info),
        raw_residuals={k2: ({kk: str(vv) for kk, vv in v.items()} if isinstance(v, dict)
                            else str(v)) for k2, v in rr.items()},
        code_version=code_version(),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
    )
    sol_path.write_text(json.dumps(sol_js, ensure_ascii=False))
    print(f"[out] moment cap {tag}: 解数据 {sol_path.relative_to(REPO)}", flush=True)
    return sol_path, dict(sdpa_info=info, solve_s=round(solve_s, 1), reused=bool(reused),
                          m=m_dim, entries=n_entries)


# ============================================================ 相位 B：认证＋证书
def certify_cap_moment(qm: QuotientMaps, mm: MomentMaps, sol: dict, k: int, tag: str,
                       E_star: Fraction, h_AA, h_AB, spot_seed: int = 97531):
    t0 = time.time()

    def rround(x):
        return dyad(x, k)

    ex = sol["exact"]
    data = dict(h_AA=list(h_AA), h_AB=list(h_AB),
                psi_AA=[rround(Fraction(s)) for s in ex["psi_AA"]],
                psi_AB=[rround(Fraction(s)) for s in ex["psi_AB"]],
                c_A=rround(Fraction(ex["c_A"])), c_B=rround(Fraction(ex["c_B"])),
                e=dyad(Fraction(ex["e"]), k, floor=True), F=[], G=[])
    shifts = {}
    for kk, mk in enumerate(qm.F_sizes):
        Mfr, dlt, _t = repair_psd(f"F{kk}", [[rround(Fraction(x)) for x in row]
                                             for row in ex["F"][kk]], k)
        shifts[f"F{kk}"] = dlt
        data["F"].append(Mfr)
    for kk, mk in enumerate(mm.sizes):
        Mfr, dlt, _t = repair_psd(f"G{kk}", [[rround(Fraction(x)) for x in row]
                                             for row in ex["G"][kk]], k)
        shifts[f"G{kk}"] = dlt
        data["G"].append(Mfr)
    B_dy = {}
    for orbit in ("AAA", "AAB", "ABC"):
        for name, _g, _m in qm.sos_def:
            key = f"{orbit}_{name}"
            Mfr, dlt, _t = repair_psd(f"B_{key}", [[rround(Fraction(x)) for x in row]
                                                   for row in ex["B"][key]], k)
            shifts[f"B_{key}"] = dlt
            B_dy[key] = Mfr
    s111 = sum(sum(row) for row in data["F"][0])
    data["c_C"] = (data["e"] + qm.s111_factor * s111
                   - qm.nrm["c_A"] * data["c_A"] - qm.nrm["c_B"] * data["c_B"]) \
        / qm.nrm["c_C"]
    R1 = {}
    for orbit in ("AAA", "AAB", "ABC"):
        lv = moment_lam(qm, mm, orbit, data)
        sv = qm.sos_sum({nm: B_dy[f"{orbit}_{nm}"] for (nm, _g, _m) in qm.sos_def})
        R1[orbit] = sum(abs(x - y) for x, y in zip(lv, sv))
    defl = sum(qm.class_counts[o] * qm.counts[o] * R1[o] for o in R1)
    certified = data["e"] - defl
    if certified <= 0:
        raise CertError(f"[{tag}] e − defl ≤ 0")

    rng = random.Random(spot_seed + k)
    lo = qm.lo
    lam_orbit = {o: moment_lam(qm, mm, o, data) for o in ("AAA", "AAB", "ABC")}
    ring = qm.ring
    for orbit in ("AAA", "AAB", "ABC"):
        lv = lam_orbit[orbit]
        ok_pts = tries = 0
        while tries < 300 and ok_pts < 8:
            tries += 1

            def rq(a, b):
                return a + (b - a) * Fraction(rng.randint(0, 64), 64)

            u, v, t = rq(lo, F1), rq(lo, F1), rq(lo, F1)
            detg = F1 + 2 * u * v * t - u * u - v * v - t * t
            if detg < 0:
                continue
            ok_pts += 1
            sos_pt = F0
            for name, gnz, mons in qm.sos_def:
                Bm = B_dy[f"{orbit}_{name}"]
                m_ = len(mons)
                zp = [(u ** e2[0]) * (v ** e2[1]) * (t ** e2[2]) for e2 in mons]
                quad = sum(Bm[p][q] * zp[p] * zp[q]
                           for p in range(m_) for q in range(m_))
                g = sum(c * (u ** eg[0]) * (v ** eg[1]) * (t ** eg[2]) for eg, c in gnz)
                if g < 0:
                    raise CertError(f"[{tag}] 抽查乘子负值 g_{name} = {g}")
                sos_pt += g * quad
            if sos_pt < 0:
                raise CertError(f"[{tag}] SOS 抽查负值（{orbit}）")
            if ring.eval3(lv, u, v, t) + R1[orbit] < 0:
                raise CertError(f"[{tag}] λ′_{orbit} 抽查 < −R1")

    if not (0 < certified <= E_star + PHI_TOL):
        raise CertError(f"[{tag}] certified = {float(certified):.15e} 违反 "
                        f"0 < c ≤ E*+1e-6（粒度 2^-{k}）")
    e_raw = Fraction(sol["exact"]["e"])
    if certified > e_raw + Fraction(1, 10 ** 9):
        raise CertError(f"[{tag}] certified > e + 1e-9（不可能）")
    print(f"[cert ] moment cap {tag}（2^-{k}）：certified = {float(certified):.12f}；"
          f"R1 = { {o: float(R1[o]) for o in R1} }，defl = {float(defl):.3e}，"
          f"认证链 {time.time() - t0:.0f}s", flush=True)
    return dict(data=data, B=B_dy, shifts=shifts, R1=R1, defl=defl,
                certified=certified, k=k)


def write_moment_certificate(qm: QuotientMaps, mm: MomentMaps, cert: dict, tag: str,
                             a0: Fraction, M, K, sol: dict, solve_info: dict,
                             out_path: Path, k_minor: int, cmdline: str,
                             anchoring: dict):
    data = cert["data"]
    dy = minorant_for(M, k_minor)
    blocks = {"M": [str(x) for x in dy["coeffs"]]}
    for name in ("psi_AA", "psi_AB"):
        blocks[f"{name}_diag"] = [str(x) for x in data[name]]
    for name in ("e", "c_A", "c_B", "c_C"):
        blocks[name] = [str(data[name])]
    for kk, m_ in enumerate(data["F"]):
        blocks[f"F{kk}"] = [[str(x) for x in row] for row in m_]
    for kk, m_ in enumerate(data["G"]):
        blocks[f"G{kk}"] = [[str(x) for x in row] for row in m_]
    for key, m_ in cert["B"].items():
        blocks[f"B_{key}"] = [[str(x) for x in row] for row in m_]
    cert_js = dict(
        kind="n9-stage-a6-momentcap",
        tag=tag,
        params=dict(a0=str(a0), M=M, K=K, cover=f"min inner product >= {a0}"),
        blocks=blocks,
        claimed_bound=str(cert["certified"]),
        provenance=dict(
            code_version=code_version(),
            seed=SEED,
            round_bits=cert["k"],
            cmdline=cmdline,
            construction=("typed (3,3,3) S₃ 商 cut 构造（typed_ladder.py 同构）＋"
                          "固定 Hermite minorant（hermite_minorant.py：φ ≥ M 于 [−1,1]）＋"
                          "KLT 引理 4.2 矩容器族 G_k ≽ 0（本文件 MomentMaps："
                          "R_k = 6S_k + (6/7)ΣS_k(·,·,1) + (3/28)δ_{k0}J，N=9 常数）"),
            minorant=dict(
                theorem=("φ(t) − H_exact(t) = φ^{(12)}(ξ)/12!·∏_k(t−ν_k)² ≥ 0；"
                         "M = 区间中点 dyadic 舍入 − W"),
                k=k_minor, W=str(dy["W"]), ncond=dy["ncond"],
                remainder=dy["remainder"]),
            containers=dict(
                lemma=("M_k(Y) = Σ_x [r_x r_xᵀ + q_x q_xᵀ] ≽ 0（ζ_y = e₁·y+i·e₂·y 于 "
                       "基点 x 的 x⊥ 正交框架；Q_k = Re ζ_y^k Re ζ_z^k + Im ζ_y^k Im ζ_z^k）"
                       "——KLT 引理 4.2，N 无关"),
                identity="(∗) Σh − e = Σ_T λ′_T + Σ_all s + Σ_k⟨G_k,M_k(Y)⟩（精确，"
                         "本文件 identity_moment_selftest）",
                sizes=list(mm.sizes), beta="6/7", gamma="3/28",
                counts=dict(triples={"AAA": "3x1", "AAB": "6x9", "ABC": "1x27"},
                            pairs={"AA": 9, "AB": 27},
                            normalization="3c_A+54c_B+27c_C = e+9·ΣF^(0)（容器不入归一化）")),
            bound_formula=("certified = e − (3R1_AAA+54R1_AAB+27R1_ABC)（无 R2 膨胀；"
                           "Σ⟨G,M_k⟩ ≥ 0 由 G ⪰ 0 精确成立＋引理 4.2）"),
            anchoring=anchoring,
            psd_shifts={k2: str(v) for k2, v in cert["shifts"].items()},
            residuals=dict(R1={o: str(v) for o, v in cert["R1"].items()},
                           defl=str(cert["defl"])),
            solver=dict(route="SDPA-GMP 7.1.3 (GMP 200-digit) + moment containers",
                        sdpa=solve_info.get("sdpa_info"),
                        reused=solve_info.get("reused")),
            solution_sha256_16=hashlib.sha256(
                json.dumps(sol["exact"], sort_keys=True).encode()).hexdigest()[:16],
            date=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        ),
    )
    out_path.write_text(json.dumps(cert_js, ensure_ascii=False, indent=1))
    return cert_js


def verify_moment_cert_file(path: Path):
    """进程外独立复核：只读 JSON → 重建（含 R_k 从零重构）→ 精确重算 certified。"""
    cert = json.loads(path.read_text())
    prm = cert["params"]
    qm = QuotientMaps(Fraction(prm["a0"]), prm["M"], prm["K"])
    mm = MomentMaps(qm)
    b = cert["blocks"]
    dy = minorant_for(prm["M"], cert["provenance"]["minorant"]["k"])
    M_coeffs = [Fraction(x) for x in b["M"]]
    if M_coeffs != dy["coeffs"]:
        fail(f"{path.name}: blocks.M ≠ hermite_minorant_dyadic 重构（固定 minorant 被篡改）")
    h_AA = pad_h(M_coeffs, qm.d_H)

    def uni(name):
        return [Fraction(x) for x in b[f"{name}_diag"]]

    data = dict(h_AA=h_AA, h_AB=h_AA,
                psi_AA=uni("psi_AA"), psi_AB=uni("psi_AB"),
                e=Fraction(b["e"][0]), c_A=Fraction(b["c_A"][0]),
                c_B=Fraction(b["c_B"][0]), c_C=Fraction(b["c_C"][0]),
                F=[[[Fraction(x) for x in row] for row in b[f"F{kk}"]]
                   for kk in range(len(qm.F_sizes))],
                G=[[[Fraction(x) for x in row] for row in b[f"G{kk}"]]
                   for kk in range(len(mm.sizes))],
                B={k2[2:]: [[Fraction(x) for x in row] for row in m_]
                   for k2, m_ in b.items() if k2.startswith("B_")})
    n_psd = 0
    for m_ in data["F"] + data["G"] + list(data["B"].values()):
        if not is_positive_definite([[x for x in row] for row in m_]):
            fail(f"{path.name}: PSD 块 LDLᵀ 失败")
        n_psd += 1
    s111 = sum(sum(row) for row in data["F"][0])
    nrm = (qm.nrm["c_A"] * data["c_A"] + qm.nrm["c_B"] * data["c_B"]
           + qm.nrm["c_C"] * data["c_C"] + qm.nrm["e"] * data["e"]
           - Fraction(qm.s111_factor) * s111)
    if nrm != 0:
        fail(f"{path.name}: 归一化残差 {nrm} ≠ 0")
    R1 = {}
    for orbit in ("AAA", "AAB", "ABC"):
        lv = moment_lam(qm, mm, orbit, data)
        sv = qm.sos_sum({nm: data["B"][f"{orbit}_{nm}"] for (nm, _g, _m) in qm.sos_def})
        R1[orbit] = sum(abs(x - y) for x, y in zip(lv, sv))
    defl = sum(qm.class_counts[o] * qm.counts[o] * R1[o] for o in R1)
    certified = data["e"] - defl
    claimed = Fraction(cert["claimed_bound"])
    if certified != claimed:
        fail(f"{path.name}: 重算 certified {float(certified):.15f} ≠ claimed "
             f"{float(claimed):.15f}")
    E_star = load_E_star()
    if not (0 < certified <= E_star + PHI_TOL):
        fail(f"{path.name}: certified 违反 0 < c ≤ E*+1e-6")
    prov = cert["provenance"]
    for field in ("round_bits", "code_version", "seed"):
        if field not in prov:
            fail(f"{path.name}: provenance 缺 {field}")
    print(f"[vcert] {path.name}: certified = {float(certified):.12f} 重算一致 ✓"
          f"（{n_psd} PSD 块 LDLᵀ（含 G 容器块）；归一化 = 0；E* − certified = "
          f"{float(E_star - certified):.9f}）", flush=True)
    return certified


def anchoring_layer(k_minor: int = 48) -> dict:
    """锚定构造对照层（KLT §6.2/引理 6.3 的降级实现，如实标注）。

    主认证路径＝dyadic 直接认证（全域证明，D6 裁定）；本层只对照报告：
    ① 值插值线性依赖：固定 Hermite minorant 在 6 节点处 M(ν_k) ≤ φ(ν_k)
       （差 ~W=2.13e-14 量级，hermite_minorant 区间证书）；
    ② E′(z*) = 0 线性依赖：tri_cap_prism 族能量在 z* 隔离区间中点的导数
       数值 ≈ 0（full_local_min 已证临界性 γ=1.79e-10，此处独立 float 复核）；
    ③ 未实现：z 的有理多项式族证书系数、99×99 Newton 修正、盒正性
       （KLT 引理 6.3）——工程量超限，按任务书降级条款如实标注。"""
    import numpy as np
    sys.path.insert(0, str(HERE.parent))
    from family import tri_cap_prism
    dy = fixed_minorant(k_minor)
    spec = None
    from hermite_minorant import load_ttp_spectrum
    spec = load_ttp_spectrum()
    node_gaps = []
    for nu in spec["nodes"]:
        t = Fraction(str(nu))
        Mv = 0.0
        for c in dy["coeffs"]:
            Mv = Mv * float(t) + float(c)           # 系数低→高 Horner
        Mv = sum(float(c) * float(t) ** d for d, c in enumerate(dy["coeffs"]))
        phi = 1.0 / math.sqrt(2.0 - 2.0 * float(t))
        node_gaps.append(phi - Mv)
    z = 0.5 * (Z_STAR_INTERVAL[0] + Z_STAR_INTERVAL[1])

    def E_fam(zz):
        X = tri_cap_prism(zz)
        D = X[:, None, :] - X[None, :, :]
        r = np.sqrt((D ** 2).sum(-1))
        iu = np.triu_indices(9, 1)
        return float(np.sum(1.0 / r[iu]))

    h = 1e-5
    dEdz = (E_fam(z + h) - E_fam(z - h)) / (2 * h)
    E_mid = E_fam(z)
    return dict(
        mode="comparison-layer（降级：dyadic 直接认证为主路径）",
        zStarInterval=list(Z_STAR_INTERVAL), z_mid=z,
        linear_dependence_1_value_interpolation=dict(
            what="固定 Hermite minorant 6 节点值插值（φ ≥ M，节点差 ~W）",
            node_gaps_phi_minus_M=node_gaps, W=str(dy["W"]),
            ok=bool(min(node_gaps) >= -1e-13)),
        linear_dependence_2_stationarity=dict(
            what="E′(z*) = 0（tri_cap_prism 族驻定性，full_local_min 已证临界性）",
            dEdz_central_float=dEdz, h=h, E_at_z_mid=E_mid,
            E_ttp_reference=float(E_TTP_TUBE),
            ok=bool(abs(dEdz) < 1e-6)),
        not_implemented=["证书系数=z 的有理多项式族", "Newton 修正（KLT §6.2 99×99）",
                          "盒正性（KLT 引理 6.3）"],
        reason="工程量超限，按任务书降级条款执行；主认证=dyadic 直接认证（全域证明，"
               "不依赖候选点取等，D6 裁定沿用），锚定层仅作对照",
    )


def run_cap_moment(a0_str: str, M: int, K: int, sdpa_bin: Path, ks=(48, 56, 64),
                   skip_solve=False, k_minor: int = 48):
    a0 = Fraction(a0_str)
    tag = rung_tag(a0)
    E_star = load_E_star()
    qm = QuotientMaps(a0, M, K)
    mm = MomentMaps(qm)
    dy = minorant_for(M, k_minor)
    h_AA = pad_h(dy["coeffs"], qm.d_H)
    sol_path = HERE / "results" / f"moment_cap_sol_{tag}_M{M}.json"
    solve_info = None
    if skip_solve:
        if not sol_path.exists():
            fail(f"--skip-solve 但解数据不存在：{sol_path}")
        print(f"[cap ] moment {tag} M={M}：复用解数据 {sol_path.relative_to(REPO)}",
              flush=True)
    else:
        if sol_path.exists():
            print(f"[cap ] moment {tag} M={M}：已有解数据，跳过求解（删文件重解）",
                  flush=True)
            solve_info = dict(reused_file=True)
        else:
            sol_path, solve_info = solve_cap_moment(a0, M, K, sdpa_bin, k_minor)
    sol = json.loads(sol_path.read_text())
    cert_name = f"n9-stage-a6-momentcap-{tag}" + (f"_M{M}.json" if M != 7 else ".json")
    cert_path = REPO / "certificates" / cert_name
    cmdline = (f"python3 numerics/bounds/moment_lift.py --cap {a0_str} "
               f"--M {M} --ks {' '.join(str(x) for x in ks)}")
    anch = anchoring_layer(k_minor)
    last_err = None
    for k in ks:
        try:
            cert = certify_cap_moment(qm, mm, sol, k, f"moment-cap-{tag}/M{M}",
                                      E_star, h_AA, h_AA)
        except CertError as exc:
            print(f"[retry] moment cap {tag} 粒度 2^-{k} 未通过：{exc}", flush=True)
            last_err = str(exc)
            continue
        write_moment_certificate(qm, mm, cert, tag, a0, M, K, sol, solve_info or {},
                                 cert_path, k_minor, cmdline, anch)
        _c = verify_moment_cert_file(cert_path)
        rung = dict(
            tag=tag, a0=a0_str, M=M, K=K,
            e_raw=float(Fraction(sol["exact"]["e"])),
            certified=str(cert["certified"]), certified_float=float(cert["certified"]),
            gap_to_E_star=float(E_star - cert["certified"]),
            gap_to_E_ttp=float(E_TTP_TUBE - cert["certified"]),
            beats_old_cap_best=bool(cert["certified"] > OLD_CAP_BEST),
            old_cap_best=str(OLD_CAP_BEST),
            round_bits=k, minorant_k=k_minor,
            R1={o: float(v) for o, v in cert["R1"].items()},
            deflation=float(cert["defl"]),
            certificate=str(cert_path.relative_to(REPO)),
            solution=str(sol_path.relative_to(REPO)),
            sdpa=sol.get("solver_info"),
            anchoring=anch,
            code_version=code_version(),
        )
        print(f"[cap ] moment {tag} M={M} ✓ certified = {rung['certified_float']:.12f}"
              f"（E* − c = {rung['gap_to_E_star']:.9f}；超旧 cap 最佳 = "
              f"{rung['beats_old_cap_best']}）", flush=True)
        return rung
    fail(f"moment cap {tag}: 全部粒度 {list(ks)} 认证失败（最后：{last_err}）")


# ============================================================ 自检总入口
def cert_chain_selftest():
    """相位 B 证书链离线自检（不跑 SDPA）：以 a5 hermite M7 已解数据注入 G=0
    （容器关闭）走 certify→write→verify 全链——certified 应复现 a5 M7 认证值
    （差仅来自 G 块的 δI PSD 修复 ~2^-40），进程外 verify 重算一致。"""
    import tempfile
    qm = QuotientMaps(Fraction(-187, 250), 7, 6)
    mm = MomentMaps(qm)
    sol_path = HERE / "results" / "hermite_cap_sol_m0748_M7.json"
    if not sol_path.exists():
        return dict(ok=True, skipped="hermite M7 解数据不在档")
    sol = json.loads(sol_path.read_text())
    sol["exact"]["G"] = [[["0"] * mk for _ in range(mk)] for mk in mm.sizes]
    E_star = load_E_star()
    dy = minorant_for(qm.M)
    h_AA = pad_h(dy["coeffs"], qm.d_H)
    cert = certify_cap_moment(qm, mm, sol, 48, "chain-selftest", E_star, h_AA, h_AA)
    anch = anchoring_layer(48)
    with tempfile.TemporaryDirectory() as td:
        out = Path(td) / "n9-stage-a6-momentcap-m0748_CHAINSELFTEST.json"
        write_moment_certificate(qm, mm, cert, "m0748", Fraction(-187, 250),
                                 7, 6, sol, dict(reused_file=True), out, 48,
                                 "selftest", anch)
        got = verify_moment_cert_file(out)
    ref = None
    cap_js = HERE / "results" / "hermite_cap.json"
    if cap_js.exists():
        for r in json.loads(cap_js.read_text()).get("rungs", []):
            if r.get("M") == 7:
                ref = Fraction(r["certified"])
    if ref is not None:
        # 差异机制口径：G=0 不是严格 PD ⟹ repair_psd 加 δI（δ=2^-40 起步），
        # 容器列 λ′ −= δΣ_kΣ_a R_k[a][a] 把 R1 抬高 ≤ δ·Σ‖R_k[a][a]‖₁。
        # certified_chain ≥ ref − 84·δΣ‖R‖₁（defl 权重 3+54+27=84）。
        delta = min(Fraction(cert["shifts"][f"G{k}"]) for k in range(mm.K))
        eps_delta = delta * sum(
            sum(abs(x) for x in mm.R[k][a][a])
            for k in range(mm.K) for a in range(mm.sizes[k]))
        diff = ref - cert["certified"]
        assert diff <= 84 * eps_delta + Fraction(1, 10 ** 12), \
            (f"证书链自检：certified 落后 a5 M7 参考 {float(diff):.2e} 超出 "
             f"G=δI 修复可解释范围 84·δΣ‖R‖₁={float(84 * eps_delta):.2e}")
        assert abs(cert["certified"] - ref) < Fraction(1, 10 ** 5)
    assert got == cert["certified"], "进程外 verify 与 certify 不一致"
    return dict(ok=True, certified=str(cert["certified"]),
                ref_hermite_M7=(str(ref) if ref is not None else None),
                diff_vs_ref=(float(ref - cert["certified"])
                             if ref is not None else None),
                deltaI_explained_bound=(float(84 * eps_delta)
                                        if ref is not None else None))


def run_selftests():
    t0 = time.time()
    rng = random.Random(SEED)
    print("[selftest] ① 容器族有效性 (6,6)：S/核和/ζ 三口径＋M_k≽0×60＋ΨR＋(∗)",
          flush=True)
    v = container_validity_selftest(6, 6, Fraction(-187, 250), 60, rng)
    print(f"[selftest] ① {v} ✓", flush=True)
    print("[selftest] ② 负对照三件（N=8 常数/篡改 S_k/非 PSD G）", flush=True)
    nc = negative_controls(6, 6, Fraction(-187, 250), rng)
    print(f"[selftest] ② {nc} ✓", flush=True)
    print("[selftest] ③ cap 约束映射 vs moment_lam 独立装配（随机数据逐行精确）",
          flush=True)
    qm = QuotientMaps(Fraction(-187, 250), 6, 6)
    mm = MomentMaps(qm)
    dy = minorant_for(qm.M)
    h_AA = pad_h(dy["coeffs"], qm.d_H)
    maps = build_cap_maps(qm, mm, h_AA, h_AA)
    chk = validate_cap_maps(qm, mm, maps, rng)
    print(f"[selftest] ③ {chk} ✓", flush=True)
    print("[selftest] ④ SDPA 导出行泛函（容器版）：G 块行/符号 vs moment_lam 独立装配",
          flush=True)
    ex = MomentCapExporter(qm, mm, h_AA, h_AA)
    rc = export_row_check_moment(qm, mm, ex, rng)
    print(f"[selftest] ④ {rc} ✓", flush=True)
    print("[selftest] ⑤ 相位 B 证书链离线自检（hermite M7 解＋G=0：certify→write→verify）",
          flush=True)
    cc = cert_chain_selftest()
    print(f"[selftest] ⑤ {cc} ✓", flush=True)
    print(f"[selftest] 完成（{time.time() - t0:.0f}s）", flush=True)
    return dict(validity=v, negative=nc, maps=chk, export_row=rc, cert_chain=cc)


def run_spot(out=HERE / "results" / "moment_lift.json", n_configs=200):
    """≥200 随机构型 M_k≽0＋恒等式＋负对照（写 results/moment_lift.json 的 spot 段）。"""
    rng = random.Random(SEED)
    lo = Fraction(-187, 250)
    v = container_validity_selftest(6, 6, lo, n_configs, rng)
    nc = negative_controls(6, 6, lo, rng)
    outd = dict(kind="moment-lift-spot", seed=SEED, code_version=code_version(),
                generated=datetime.now(timezone.utc).isoformat(timespec="seconds"),
                spot=v, negative_controls=nc)
    p = Path(out)
    p.parent.mkdir(parents=True, exist_ok=True)
    if p.exists():
        db = json.loads(p.read_text())
        db.update(outd)
    else:
        db = outd
    p.write_text(json.dumps(db, indent=1, default=str) + "\n")
    print(f"[out] 已写 {p}", flush=True)
    return db


# ============================================================ 主流程
def main() -> None:
    ap = argparse.ArgumentParser(description="R7-1 矩容器抬天花板（moment lift）")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--spot", action="store_true")
    ap.add_argument("--probe", action="store_true")
    ap.add_argument("--probe-replay", action="store_true",
                    help="探针重放：跑完在 stdout 追加 ===PROBE-REPLAY-JSON=== 段"
                         "（验收门 ① 用；需与 --probe 同给）")
    ap.add_argument("--no-anchored", action="store_true",
                    help="跳过锚定探针（验收门 ① 的快速重放口径）")
    ap.add_argument("--probe-tiers", type=str, default=None,
                    help="';' 分隔的 M,K 档（默认 5,4;6,6;7,6）")
    ap.add_argument("--cap", help="cap 档，如 -0.748（相位 B）")
    ap.add_argument("--anchor-cap", metavar="ARM",
                    help="R8-2 锚定探针臂：A=(7,6)+容器 / B=(9,6)+容器 / "
                         "C=(9,6) 无容器（仅 B 停滞/发散时诊断）")
    ap.add_argument("--anchor-finalize", action="store_true",
                    help="从存档 sol 重算全部臂并写 anchor_probe_m9.json（幂等）")
    ap.add_argument("--anchor-out", default=None, help="锚定探针账本路径")
    ap.add_argument("--anchor-check", action="store_true",
                    help="锚定导出行泛函自检（selftest ④ 口径，小档快速）")
    ap.add_argument("--M", type=int, default=8)
    ap.add_argument("--K", type=int, default=6)
    ap.add_argument("--ks", type=int, nargs="+", default=[48, 56, 64])
    ap.add_argument("--k-minor", type=int, default=48)
    ap.add_argument("--skip-solve", action="store_true")
    ap.add_argument("--verify-cert", help="证书独立复核")
    ap.add_argument("--out", default=str(HERE / "results" / "moment_lift.json"))
    ap.add_argument("--sdpa-bin", default=os.environ.get(
        "SDPA_GMP_BIN", "/tmp/hpbuild/sdpa-gmp-7.1.3/sdpa_gmp"))
    args = ap.parse_args()
    sdpa_bin = Path(args.sdpa_bin)

    if args.selftest:
        run_selftests()
        return
    if args.anchor_check:
        rng = random.Random(SEED_ANCHOR)
        for (M, K, cont) in ((6, 6, True), (7, 6, False)):
            qm = QuotientMaps(Fraction(-187, 250), M, K)
            mm = MomentMaps(qm)
            dy = minorant_for(M)
            h_AA = pad_h(dy["coeffs"], qm.d_H)
            Gram, _z = ttp_anchor_gram()
            ex = AnchoredCapExporter(qm, mm, h_AA, h_AA, Gram,
                                     containers=cont)
            rc = export_row_check_anchor(qm, mm, ex, rng)
            print(f"[anchor-check] ({M},{K}) containers={cont}: {rc} "
                  f"rows(m={ex.m}) anchor_rows={ex.n_anchor_rows} ✓", flush=True)
        return
    if args.anchor_finalize:
        run_anchor_finalize(out=Path(args.anchor_out) if args.anchor_out else None)
        return
    if args.anchor_cap:
        if args.anchor_cap not in ANCHOR_ARM_SPECS:
            ap.error(f"--anchor-cap 取 A/B/C（got {args.anchor_cap}）")
        if not (sdpa_bin.exists() and os.access(sdpa_bin, os.X_OK)):
            fail(f"sdpa_gmp 不可执行：{sdpa_bin}")
        spec = ANCHOR_ARM_SPECS[args.anchor_cap]
        a0 = Fraction(args.cap) if args.cap else Fraction(-187, 250)
        solve_anchored_cap(a0, spec["M"], spec["K"], sdpa_bin, args.anchor_cap,
                           groups=spec["groups"], containers=spec["containers"],
                           k_minor=args.k_minor)
        run_anchor_finalize(out=Path(args.anchor_out) if args.anchor_out else None)
        return
    if args.spot:
        run_spot(out=args.out)
        return
    if args.probe:
        tiers = ([(int(t.split(",")[0]), int(t.split(",")[1]))
                  for t in args.probe_tiers.split(";")]
                 if args.probe_tiers else None)
        outd = run_probe(tiers=tiers, out=args.out,
                         with_anchored=not args.no_anchored)
        if args.probe_replay:
            import sys as _sys
            _sys.stdout.write("===PROBE-REPLAY-JSON===\n"
                              + json.dumps(dict(tiers=outd["tiers"],
                                                verdict=outd["verdict"]),
                                           default=str) + "\n")
        return
    if args.verify_cert:
        p = Path(args.verify_cert)
        if "momentcap" in p.name:
            verify_moment_cert_file(p)
        else:
            fail(f"无法识别证书类型：{p.name}")
        return
    if args.cap:
        if not (sdpa_bin.exists() and os.access(sdpa_bin, os.X_OK)):
            fail(f"sdpa_gmp 不可执行：{sdpa_bin}")
        row = run_cap_moment(args.cap, args.M, args.K, sdpa_bin, ks=tuple(args.ks),
                             skip_solve=args.skip_solve, k_minor=args.k_minor)
        out = Path(args.out)
        db = json.loads(out.read_text()) if out.exists() else {}
        db.setdefault("cap_rungs", [])
        by_key = {f"{r['tag']}_M{r['M']}": r for r in db["cap_rungs"]}
        by_key[f"{row['tag']}_M{row['M']}"] = row
        db["cap_rungs"] = list(by_key.values())
        db["kind"] = db.get("kind", "moment-lift")
        db["script"] = "moment_lift.py"
        db["code_version"] = code_version()
        db["E_star"] = float(load_E_star())
        db["E_ttp_tube"] = float(E_TTP_TUBE)
        db["old_cap_best"] = float(OLD_CAP_BEST)
        db["cap_updated"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
        out.write_text(json.dumps(db, ensure_ascii=False, indent=1))
        print(f"[out] 已写 {out}", flush=True)
        return
    ap.error("需要 --selftest / --spot / --probe / --cap / --verify-cert")


if __name__ == "__main__":
    main()
