#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""slab_band.py — N=9 slab 带（最小内积 m ∈ [lo,hi] ⊆ [−1,−0.9]）的 typed 三点证书。

机制自 N=7 证明的 Case 2（references/thomson-n7-lean/paper/PAPER.md §6–7.1）移植：
slab 带不含候选 TTP（其最小内积 m* = −0.7475605 > −0.9），故每片可拿到
**正裕度** certified > E*——这是与主战场（任何含 TTP 的切口上界恒 ≤ E*）的本质区别。

## 移植的 typed 三点界（PAPER.md §6，n 参数化，n=9）

设 (0,1) 为最小内积对（**极点**，type P；重排可得，PAPER.md §6.4/exists_minpair_perm），
其余 n−2 = 7 个顶点为**环**（type R）。对类：A＝极点对（1 对）、B＝极点–环（14 对）、
C＝环–环（21 对）；无序三点：PPR（7 个）、PRR（42 个）、RRR（35 个），合 84 = C(9,3)。

自由数据：三条类 minorant H_A,H_B,H_C（次数 d_H）、两条 share 多项式 ψ_Ba,ψ_Cb、
常数 e,c_α,c_β（c_γ 由计数条件定）、两族 PSD 块 F_P^(k),F_R^(k)（k<K，尺寸 M−k）。

  s_X(u,v,t) = Σ_k⟨F_X^(k), Y_k(u,v,t)⟩，Y_k[a,b] = u^a v^b Q_k（**不**对称化；
    核递推同引理 4.1：Q_0=1, Q_1=t−uv, Q_{k+2}=2(t−uv)Q_{k+1}−(1−u²)(1−v²)Q_k）
  gm_X(t) = s_X(1,t,t)+s_X(t,1,t)+s_X(t,t,1)
  Ψ_A = H_A − 2gm_P，Ψ_B = H_B − gm_P − gm_R，Ψ_C = H_C − 2gm_R
  share（每个对在各第三顶点的份额，行和恰为该对之 Ψ，n=9 分母 7/6/5）：
    对 A 在 7 个环顶点各 Ψ_A/7；对 B 在另一极点 ψ_Ba、在 6 个其余环顶点各 (Ψ_B−ψ_Ba)/6；
    对 C 在 2 个极点各 ψ_Cb、在 5 个其余环顶点各 (Ψ_C−2ψ_Cb)/5
  逐无序三点的 slack（PAPER.md §6.2 的 λ；u,v,t 为该三点内积，顺序见下）：
    λ_A(u,v,t) = Ψ_A(u)/7 + ψ_Ba(v) + ψ_Ba(t) − c_α
                 − 2(s_P(u,v,t)+s_P(u,t,v)+s_R(v,t,u))          [PPR: u=t_01]
    λ_B(u,v,t) = (Ψ_B−ψ_Ba)(u)/6 + (Ψ_B−ψ_Ba)(v)/6 + ψ_Cb(t) − c_β
                 − 2(s_P(u,v,t)+s_R(u,t,v)+s_R(v,t,u))          [PRR]
    λ_Γ(u,v,t) = Σ_{x∈{u,v,t}} (Ψ_C−2ψ_Cb)(x)/5 − c_γ
                 − 2(s_R(u,v,t)+s_R(u,t,v)+s_R(v,t,u))          [RRR]
  计数条件（n=9）：7c_α + 42c_β + 35c_γ = e + 2s_P(1,1,1) + 7s_R(1,1,1)
    （s_X(1,1,1) = F_X^(0) 全元素和，因 Q_k(1,1,1)=δ_{k0}）

**组合恒等式**（PAPER.md §6.3 的推导，本脚本以纯 Fraction 在随机有理构型上精确
自检 ==0；对任意 (H,ψ,c,e,F) 的多项式恒等式，与 λ 是否 ≥0 无关）：

    Σ_{i<j} H_cls(t_ij) − e = Σ_{T 无序} λ_T(T) + Σ_all，
    Σ_all := Σ_{i,j,l} s_type(i)(t_ij,t_il,t_jl) ≥ 0   （引理 4.1 ＋ F ⪰ 0）

  λ ≥ 0 于出现的三点域 ⟹ ΣH ≥ e；H_X ≤ φ ⟹ E ≥ e。n=9 的域（PAPER.md §6.4）：
    λ_A：Gram 三点，lo ≤ u ≤ hi，v,t ≥ lo（u 是最小对内积）；
    λ_B/λ_Γ：Gram 三点，全部 ≥ lo。
    minorant：H_A ≤ φ 于 [lo,hi]，H_B,H_C ≤ φ 于 [lo,1)。
  （TTP 的 m*=−0.7476 > hi ≤ −0.9，故被排除在一切 slab 域外——正裕度的来源。）

## SDP（数值阶段）

在 (h_A,h_B,h_C,ψ_Ba,ψ_Cb,e,c_α,c_β, F_P,F_R ⪰ 0, 各 λ 的 SOS Gram 块 ⪰ 0,
minorant 块 ⪰ 0) 上最大化 e，约束为 6 条多项式恒等式（逐系数）：
  (i)  λ_A = Σ_r g_r·z_rᵀB_r z_r，g_r ∈ {1, u−lo, v−lo, t−lo, hi−u, detG}
       （z_r 次数 ≤ ⌊(D−deg g_r)/2⌋；N7 §6.5 的 6 块布局；hi−u 即带上切口，
        正是 slab 证书可行、且 e 可超 E* 的机制）；
  (ii) λ_B = λ_Γ = 同型 5 块（仅下切口：1, u−lo, v−lo, t−lo, detG）；
  (iii) minorant Lukács 型（PAPER.md (4)）：
       H_B,H_C（[lo,1)，y∈[0,b]，b²=(1−lo)/2）：
         1−2yH(1−2y²) = σ_0 + yσ_1 + (b²−y²)(σ_2+yσ_3)；
       H_A（[lo,hi]，y∈[c,b]，c²=(1−hi)/2，双侧，N7 SlabOneD 同型）：
         1−2yH_A(1−2y²) = τ_0 + yτ_1 + (y²−c²)(τ_2+yτ_4) + (b²−y²)(τ_3+yτ_5)。

## 严格化（exact 阶段，对齐 sdp_certify.py 的"舍入＋精确残差折减"模式）

  1) dyadic 舍入（分母 2^k）：h/ψ/c 最近舍入；e 向下；F/SOS/minorant 块最近舍入后
     +δI PSD 修复（exact.py 无主元 LDLᵀ 验证严格正定）；c_γ 由计数条件以 Fraction
     精确重算。
  2) 精确残差（纯 Fraction，逐单项式系数）：
       R1_X = ‖λ_X − SOS_X‖₁（域上 |u|,|v|,|t| ≤ 1 ⇒ 逐点 |resid| ≤ R1_X）
       R2_X = Σ_j |r_{X,j}|·ŵ^j（resid_σ 于 y ∈ [0,ŵ]，ŵ 为 ≥ b 的有理上界）
  3) 界值（对一切最小内积 m ∈ [lo,hi] 的 n 点构型）：
       certified = (e − (7·R1_A + 42·R1_B + 35·R1_Γ)) / (1 + max(R2_A,R2_B,R2_C))
     推导：ΣH − e = Σ_T λ_T + Σ_all ≥ −(7R1_A+42R1_B+35R1_Γ)（Σ_all ≥ 0）；
     E = Σφ ≥ ΣH_cls/(1+R2_max) ≥ certified。
  4) 证书 certificates/n9-stage-a2-slab-<tag>.json（thomson_certs/schema.py 格式，
     全 'p/q' 字符串）；回读 decode → 重建 → 精确重算 certified 逐位比对；
     --verify-cert 进程外独立复核（只读 JSON）。

断言（违反打印原因并 sys.exit(1)）：精确组合恒等式自检；引理 4.1 typed 正性自检；
全部 PSD 块 LDLᵀ 正定；certified > E*（**正裕度，slab 带的核心断言**）；
certified ≤ 数值 e + 1e-9（舍入只损失）；回读重算逐位一致。

## N=7 校准（--calib7）

同一代码 n=7、(M,K)=(6,6)、slab [−0.99,−0.98]（N7 论文 slab 1）：N7 的证书是该
松弛的可行点（同 6/5/5 SOS 布局、同 minorant 模族），故 SDP 最优 ≥ 其 e =
E(P)+2.5858e−6；断言 e > E(P)（正裕度方向）且 |e − 14.45298| ≤ 5e-3。这是
typed 移植正确性对 N=7 已验证机制的最强校准。

用法（thomson-n9 下）：
  numerics/.venv/bin/python numerics/bounds/slab_band.py --selftest   # 精确自检（无需 cvxpy）
  numerics/.venv/bin/python numerics/bounds/slab_band.py --calib7     # N=7 校准 ~数分钟
  numerics/.venv/bin/python numerics/bounds/slab_band.py              # 3 片默认全流程
  numerics/.venv/bin/python numerics/bounds/slab_band.py --slabs "-0.95:-0.93" --config small
  python3 numerics/bounds/slab_band.py --verify-cert certificates/n9-stage-a2-slab-s1.json
依赖：numpy/scipy（装配/自检）；cvxpy+Clarabel 仅求解路径；认证路径纯标准库＋Fraction。
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]                                    # .../thomson-n9
WORKFLOW_CERTS = HERE.parents[2] / "thomson-workflow" / "certificates"
sys.path.insert(0, str(HERE))                             # sdp_bound / sdp_certify
sys.path.insert(0, str(WORKFLOW_CERTS))                   # thomson_certs

import sdp_bound                                          # noqa: E402
from sdp_certify import (dyad, repair_psd,                # noqa: E402
                         rational_point, random_dyadic_config)
from thomson_certs.exact import is_positive_definite      # noqa: E402
from thomson_certs.schema import (                        # noqa: E402
    Certificate, decode_certificate, encode_certificate, fraction_to_str)

F0, F1 = Fraction(0), Fraction(1)

CFG = dict(
    N=9,
    SEED=20261004,
    CONFIGS=dict(sdp_bound.CFG["CONFIGS"]),               # small/medium/midlarge/large
    N7CONFIG=(6, 6),                                      # N7 slab 的 (M,K)（F 尺寸 6..1）
    DEFAULT_SLABS=[Fraction(-1), Fraction(-99, 100),
                   Fraction(-97, 100), Fraction(-95, 100)],   # 3 片的 4 个端点
    DEFAULT_CONFIG="medium",
    SOLVER=dict(max_iter=1000, tol_gap_abs=1e-8, tol_gap_rel=1e-8,
                tol_feas=1e-8, time_limit=420.0),
    FALLBACK=dict(eps=1e-9, max_iters=30000, time_limit_secs=420.0),
    K_LIST=[40, 48, 56],                                  # dyadic 粒度候选
    ACCEPT=dict(identity_residual=1e-5, slack_min=-1e-6, min_eig=-1e-7),
    GRID_NTRIPLE=20000,
    GRID_NT=20001,
    CALIB7=dict(N=7, lo=Fraction(-99, 100), hi=Fraction(-49, 50),
                expect=14.4529800, tol=5e-3),             # N7 slab 1 的 e（PAPER.md §6.5）
)

E_STAR_FALLBACK = 25.759986531
N7_ESTAR = Fraction("14.45297741422134")                  # E(P)（PAPER.md §2，40 位截 17 位）


def fail(msg: str) -> None:
    print(f"[FAIL] {msg}", flush=True)
    sys.exit(1)


def load_E_star() -> tuple[Fraction, str]:
    p = HERE.parents[2] / "thomson-workflow" / "data" / "energies.json"
    try:
        with open(p) as f:
            v = json.load(f)["energies"]["9"]["value"]
        return Fraction(v), str(p)
    except Exception as exc:
        print(f"[warn] energies.json 不可读（{exc}），用常数 {E_STAR_FALLBACK}", flush=True)
        return Fraction(E_STAR_FALLBACK), f"fallback 常数（{exc}）"


# ============================================================ 核心 maps（Fraction 主本，结构对 n 参数化）
class TypedCore:
    """Y_k 列、三类 λ 的核映射、gm 映射——全部纯 Fraction（系数实为整数/小分子有理数）。

    sdp_bound.Poly3 只取其单项式索引结构（mons/index/perm_maps 为整数）；
    系数一律以 Fraction 重算，供 SDP（转 float）与 exact 认证共用同一主本。
    """

    def __init__(self, n: int, M: int, K: int):
        assert n >= 5, "typed 结构需要 ring = n−2 ≥ 3"
        Dl = 2 * M - 2
        self.n, self.M, self.K, self.D, self.d_H = n, M, K, Dl, Dl
        self.ring_n = n - 2
        self.dA, self.dB, self.dC = self.ring_n, self.ring_n - 1, self.ring_n - 2
        self.nPPR = self.ring_n
        self.nPRR = 2 * (self.ring_n * (self.ring_n - 1) // 2)
        self.nRRR = self.ring_n * (self.ring_n - 1) * (self.ring_n - 2) // 6
        ring = sdp_bound.Poly3(Dl)
        self.ring = ring
        self.nmon = ring.nmon
        self.F_sizes = [M - k for k in range(K)]

        def zero():
            return [F0] * self.nmon

        def mono(e, c=F1):
            v = zero()
            v[ring.index[e]] = c
            return v

        def mul(av, bv):
            out = zero()
            for p, ca in enumerate(av):
                if ca == 0:
                    continue
                ep = ring.mons[p]
                for q, cb in enumerate(bv):
                    if cb == 0:
                        continue
                    eq = ring.mons[q]
                    out[ring.index[(ep[0] + eq[0], ep[1] + eq[1], ep[2] + eq[2])]] += ca * cb
            return out

        t_m_uv = [x - y for x, y in zip(mono((0, 0, 1)), mono((1, 1, 0)))]
        om = [x + y for x, y in zip(
            [x - y for x, y in zip(
                [x - y for x, y in zip(mono((0, 0, 0)), mono((2, 0, 0)))],
                mono((0, 2, 0)))], mono((2, 2, 0)))]      # (1−u²)(1−v²)
        Qs = [mono((0, 0, 0)), t_m_uv]
        while len(Qs) < K:
            prev1 = [2 * x for x in mul(t_m_uv, Qs[-1])]
            prev2 = mul(om, Qs[-2])
            Qs.append([x - y for x, y in zip(prev1, prev2)])
        self.Qs = Qs[:K]
        # 回归自检 1：Q_k 对 (u,v) 对称（om 的符号写反时 Q_2 起不对称——发生过，
        # 恒等式自检抓出）；自检 2：与 sdp_bound.build_Q（浮点主本）逐系数一致。
        for k, Q in enumerate(self.Qs):
            a = self.eval3(Q, Fraction(1, 3), Fraction(2, 5), Fraction(-1, 7))
            b = self.eval3(Q, Fraction(2, 5), Fraction(1, 3), Fraction(-1, 7))
            assert a == b, f"Q_{k} 不对称于 (u,v)——核递推装配有 bug"
        Qf = sdp_bound.build_Q(ring, K)
        for k in range(K):
            for p in range(self.nmon):
                assert float(self.Qs[k][p]) == Qf[k][p], \
                    f"Q_{k} 与 sdp_bound.build_Q 不一致 @mon {ring.mons[p]}"

        # Y_k 列（不对称化）与索引
        self.Y_cols, self.Y_index = [], {}
        for k in range(K):
            for a_ in range(M - k):
                for b_ in range(M - k):
                    self.Y_index[(k, a_, b_)] = len(self.Y_cols)
                    self.Y_cols.append(mul(mono((a_, b_, 0)), Qs[k]))

        def perm(vec, which):
            pm = ring.perm_maps[which]
            return [vec[pm[j]] for j in range(self.nmon)]

        def subst_keep(vec, keep):
            """u^i v^j t^l → x^{keep 内指数之和}（放 slot 0），其余变量置 1。"""
            out = zero()
            for p, c in enumerate(vec):
                if c == 0:
                    continue
                i, j, l = ring.mons[p]
                d = (i if keep[0] else 0) + (j if keep[1] else 0) + (l if keep[2] else 0)
                out[ring.index[(d, 0, 0)]] += c
            return out

        # gm 列：Y(1,x,x)+Y(x,1,x)+Y(x,x,1)
        self.gm_cols = [[x + y for x, y in zip(
            [x + y for x, y in zip(subst_keep(Y, (False, True, True)),
                                   subst_keep(Y, (True, False, True)))],
            subst_keep(Y, (True, True, False)))]
            for Y in self.Y_cols]

        # 三类 λ 的核映射（含 share 的 gm 部分；const/share/h 部分在 LamMaps）
        # 工具：把 slot0 单变量向量（形如 x^d 于 (d,0,0)）放到指定 slot
        def univ_to_slot(vec, slot):
            out = zero()
            for p, c in enumerate(vec):
                if c == 0:
                    continue
                d = ring.mons[p][0]
                e = [0, 0, 0]
                e[slot] = d
                out[ring.index[tuple(e)]] += c
            return out

        rdA, rdB, rdC = Fraction(1, self.dA), Fraction(1, self.dB), Fraction(1, self.dC)
        # KA: F_P: −2(Y+p3)−(2/dA)gm_P@u ；F_R: −2 p5
        # KB: F_P: −2Y−(1/dB)(gm_P@u+gm_P@v)；F_R: −2(p3+p5)−(1/dB)(gm_R@u+gm_R@v)
        # KG: F_R: −2(Y+p3+p5)−(2/dC)(gm_R@u,v,t)；另 F_P0/F_R0 的 s111 项在 LamMaps 加
        def neg2sum(terms):
            acc = zero()
            for t in terms:
                acc = [x + y for x, y in zip(acc, t)]
            return [-2 * x for x in acc]

        self.KA_P, self.KA_R, self.KB_P, self.KB_R, self.KG_R = [], [], [], [], []
        for idx in range(len(self.Y_cols)):
            Y = self.Y_cols[idx]
            Y3, Y5 = perm(Y, 3), perm(Y, 5)
            gm = self.gm_cols[idx]
            self.KA_P.append([x + y for x, y in zip(
                neg2sum([Y, Y3]),
                [-(2 * rdA) * c for c in univ_to_slot(gm, 0)])])
            self.KA_R.append(neg2sum([Y5]))
            gB = [x + y for x, y in zip(univ_to_slot(gm, 0), univ_to_slot(gm, 1))]
            self.KB_P.append([x + y for x, y in zip(
                neg2sum([Y]), [-(1 * rdB) * c for c in gB])])
            self.KB_R.append([x + y for x, y in zip(
                neg2sum([Y3, Y5]), [-(1 * rdB) * c for c in gB])])
            gC = [x + y for x, y in zip(
                univ_to_slot(gm, 0), [x + y for x, y in zip(
                    univ_to_slot(gm, 1), univ_to_slot(gm, 2))])]
            self.KG_R.append([x + y for x, y in zip(
                neg2sum([Y, Y3, Y5]), [-(2 * rdC) * c for c in gC])])

    # ---------------- 求值 ----------------
    def eval3(self, vec, u, v, t):
        ring = self.ring
        pu = [F1] + [None] * self.D
        pv = [F1] + [None] * self.D
        pt = [F1] + [None] * self.D
        for i in range(1, self.D + 1):
            pu[i] = pu[i - 1] * u
            pv[i] = pv[i - 1] * v
            pt[i] = pt[i - 1] * t
        acc = F0
        for p, c in enumerate(vec):
            if c:
                i, j, l = ring.mons[p]
                acc += c * pu[i] * pv[j] * pt[l]
        return acc

    def eval1(self, coeffs, x):
        acc = F0
        xp = F1
        for c in coeffs:
            acc += c * xp
            xp *= x
        return acc

    def vec_to_float(self, vec):
        return np.array([float(x) for x in vec])

    def cols_to_float(self, cols):
        return np.array([[float(x) for x in col] for col in cols]).T   # (nmon × ncols)


def unit_exp(slot):
    e = [0, 0, 0]
    e[slot] = 1
    return tuple(e)


# ============================================================ slab 装配（lo/hi 依赖部分）
class LamMaps:
    """三类 λ 对 (h,ψ,e,c,F) 的仿射映射、SOS 块定义、minorant 映射（Fraction 主本）。"""

    def __init__(self, core: TypedCore, lo: Fraction, hi: Fraction):
        self.core, self.lo, self.hi = core, lo, hi
        ring, nmon = core.ring, core.nmon
        d_H = core.d_H
        self.nPPR, self.nPRR, self.nRRR = core.nPPR, core.nPRR, core.nRRR
        rdA = Fraction(1, core.dA)
        rdB = Fraction(1, core.dB)
        rdC = Fraction(1, core.dC)

        def zeros(rows, cols):
            return [[F0] * cols for _ in range(rows)]

        def add_h(Mx, slot, scale):
            for j in range(d_H + 1):
                e = [0, 0, 0]
                e[slot] = j
                Mx[ring.index[tuple(e)]][j] += scale

        # ---- λ_A：h_A（slot u，+1/dA）、ψ_Ba（slots v,t，+1）、c_α（−1）----
        self.MA_hA = zeros(nmon, d_H + 1)
        add_h(self.MA_hA, 0, rdA)
        self.MA_psiBa = zeros(nmon, d_H + 1)
        add_h(self.MA_psiBa, 1, F1)
        add_h(self.MA_psiBa, 2, F1)
        self.MA_cA = [F0] * nmon
        self.MA_cA[ring.index[(0, 0, 0)]] = Fraction(-1)
        # ---- λ_B：h_B（slots u,v，+1/dB）、ψ_Ba（slots u,v，−1/dB）、ψ_Cb（slot t，+1）、c_β（−1）
        self.MB_hB = zeros(nmon, d_H + 1)
        add_h(self.MB_hB, 0, rdB)
        add_h(self.MB_hB, 1, rdB)
        self.MB_psiBa = zeros(nmon, d_H + 1)
        add_h(self.MB_psiBa, 0, -rdB)
        add_h(self.MB_psiBa, 1, -rdB)
        self.MB_psiCb = zeros(nmon, d_H + 1)
        add_h(self.MB_psiCb, 2, F1)
        self.MB_cB = [F0] * nmon
        self.MB_cB[ring.index[(0, 0, 0)]] = Fraction(-1)
        # ---- λ_Γ：h_C（slots u,v,t，+1/dC）、ψ_Cb（slots u,v,t，−2/dC）、−c_γ ----
        # c_γ = (e + sP111 + ring_n·sR111 − nPPR·c_α − nPRR·c_β)/nRRR
        self.MG_hC = zeros(nmon, d_H + 1)
        for s in range(3):
            add_h(self.MG_hC, s, rdC)
        self.MG_psiCb = zeros(nmon, d_H + 1)
        for s in range(3):
            add_h(self.MG_psiCb, s, -2 * rdC)
        inv_R = Fraction(1, core.nRRR)
        self.MG_e = [F0] * nmon
        self.MG_e[ring.index[(0, 0, 0)]] = -inv_R
        self.MG_cA = [F0] * nmon
        self.MG_cA[ring.index[(0, 0, 0)]] = Fraction(core.nPPR, core.nRRR)
        self.MG_cB = [F0] * nmon
        self.MG_cB[ring.index[(0, 0, 0)]] = Fraction(core.nPRR, core.nRRR)
        # s111 项：−2·sP111/nRRR − ring_n·sR111/nRRR 进入 F_P[0]/F_R[0] 的每元素
        # （计数条件 (6)：nRRR·c_γ 含 e + 2·s_P(1,1,1) + ring_n·s_R(1,1,1)）
        self.MG_s111_FP0 = [[-2 * inv_R] * core.F_sizes[0]
                            for _ in range(core.F_sizes[0])]
        self.MG_s111_FR0 = [[-inv_R * core.ring_n] * core.F_sizes[0]
                             for _ in range(core.F_sizes[0])]

        # ---- SOS 块（u,v,t 域乘子）----
        def mons_upto(dmax):
            return [e for e in ring.mons if sum(e) <= dmax]

        detG = [((0, 0, 0), F1), ((1, 1, 1), Fraction(2)), ((2, 0, 0), Fraction(-1)),
                ((0, 2, 0), Fraction(-1)), ((0, 0, 2), Fraction(-1))]
        D = core.D
        cut = lambda slot: [((0, 0, 0), -lo), (unit_exp(slot), F1)]
        hicut = [((0, 0, 0), hi), (unit_exp(0), Fraction(-1))]
        self.sosA = [("1", [((0, 0, 0), F1)], mons_upto(D // 2)),
                     ("u-lo", cut(0), mons_upto((D - 1) // 2)),
                     ("v-lo", cut(1), mons_upto((D - 1) // 2)),
                     ("t-lo", cut(2), mons_upto((D - 1) // 2)),
                     ("hi-u", hicut, mons_upto((D - 1) // 2)),
                     ("detG", detG, mons_upto((D - 3) // 2))]
        self.sosB = [("1", [((0, 0, 0), F1)], mons_upto(D // 2)),
                     ("u-lo", cut(0), mons_upto((D - 1) // 2)),
                     ("v-lo", cut(1), mons_upto((D - 1) // 2)),
                     ("t-lo", cut(2), mons_upto((D - 1) // 2)),
                     ("detG", detG, mons_upto((D - 3) // 2))]
        self.sosG = list(self.sosB)

        # ---- minorant 映射（p_X(y) = 1 − 2y·H_X(1−2y²)）----
        self.deg_p = 2 * d_H + 1
        self.Csub = [[F0] * (d_H + 1) for _ in range(self.deg_p + 1)]
        for i in range(d_H + 1):
            for m in range(i + 1):
                self.Csub[2 * m][i] += Fraction(math.comb(i, m) * ((-2) ** m))
        self.Cp = [[F0] * (d_H + 1) for _ in range(self.deg_p + 1)]
        for r in range(1, self.deg_p + 1, 2):
            self.Cp[r] = [-2 * x for x in self.Csub[r - 1]]
        self.p_const = [F0] * (self.deg_p + 1)
        self.p_const[0] = F1
        self.b2 = (F1 - lo) / 2
        self.c2 = (F1 - hi) / 2
        # σ（H_B,H_C，[0,b]）：PAPER.md (4)
        self.sig_def = [("sig0", list(range(0, d_H + 1)), [(0, F1)]),
                        ("sig1", list(range(0, d_H + 1)), [(1, F1)]),
                        ("sig2", list(range(0, d_H)), [(0, self.b2), (2, Fraction(-1))]),
                        ("sig3", list(range(0, d_H)),
                         [(1, self.b2), (3, Fraction(-1))])]
        # τ（H_A，[c,b] 双侧；乘子 y、y²−c²、b²−y² 及其奇积，N7 SlabOneD 模族）
        self.tau_def = [("tau0", list(range(0, d_H + 1)), [(0, F1)]),
                        ("tau_y", list(range(0, d_H + 1)), [(1, F1)]),
                        ("tau_c", list(range(0, d_H)), [(0, -self.c2), (2, F1)]),
                        ("tau_b", list(range(0, d_H)), [(0, self.b2), (2, Fraction(-1))]),
                        ("tau_yc", list(range(0, d_H)),
                         [(1, -self.c2), (3, F1)]),
                        ("tau_yb", list(range(0, d_H)),
                         [(1, self.b2), (3, Fraction(-1))])]
        # R2 权重 ŵ：≥ b = √b2 的有理上界（isqrt；完全平方时取精确值——
        # lo=−1 时 b2=1，若无条件 +1 会得 ŵ=2，残差权重被 2^j 灾难性放大）
        p, q = self.b2.numerator, self.b2.denominator
        s = math.isqrt(p * q)
        self.w_hat = Fraction(s if s * s == p * q else s + 1, q)

    # ---------------- λ / SOS / minorant 的精确装配 ----------------
    def lam(self, which: str, data: dict) -> list[Fraction]:
        """从证书数据（全 Fraction）装配 λ_X 的单项式系数向量。

        data 键：hA,hB,hC,psiBa,psiCb,e,cA,cB,FP（list of mat）,FR。
        """
        core = self.core
        ring = core.ring
        out = [F0] * core.nmon

        def add_mat(Mx, x):
            for i in range(core.nmon):
                row = Mx[i]
                acc = F0
                for j in range(len(x)):
                    if row[j]:
                        acc += row[j] * x[j]
                out[i] += acc

        def add_cols(cols, mats):
            for k, m_k in enumerate(core.F_sizes):
                Mk = mats[k]
                off = 0
                for kk in range(k):
                    off += core.F_sizes[kk] ** 2
                for idx in range(m_k * m_k):
                    col = cols[off + idx] if isinstance(cols, list) else None
                    a_, b_ = divmod(idx, m_k)
                    c = Mk[a_][b_]
                    if c == 0:
                        continue
                    for p, cc in enumerate(col):
                        if cc:
                            out[p] += c * cc

        if which == "A":
            add_mat(self.MA_hA, data["hA"])
            add_mat(self.MA_psiBa, data["psiBa"])
            out[ring.index[(0, 0, 0)]] += self.MA_cA[ring.index[(0, 0, 0)]] * data["cA"]
            add_cols(core.KA_P, data["FP"])
            add_cols(core.KA_R, data["FR"])
        elif which == "B":
            add_mat(self.MB_hB, data["hB"])
            add_mat(self.MB_psiBa, data["psiBa"])
            add_mat(self.MB_psiCb, data["psiCb"])
            out[ring.index[(0, 0, 0)]] += self.MB_cB[ring.index[(0, 0, 0)]] * data["cB"]
            add_cols(core.KB_P, data["FP"])
            add_cols(core.KB_R, data["FR"])
        elif which == "G":
            add_mat(self.MG_hC, data["hC"])
            add_mat(self.MG_psiCb, data["psiCb"])
            const = ring.index[(0, 0, 0)]
            out[const] += (self.MG_e[const] * data["e"]
                           + self.MG_cA[const] * data["cA"]
                           + self.MG_cB[const] * data["cB"])
            for k, m_k in enumerate(core.F_sizes):
                for a_ in range(m_k):
                    for b_ in range(m_k):
                        w = self.MG_s111_FP0[a_][b_] if k == 0 else F0
                        if w and data["FP"][0][a_][b_]:
                            out[const] += w * data["FP"][0][a_][b_]
            for a_ in range(core.F_sizes[0]):
                for b_ in range(core.F_sizes[0]):
                    w = self.MG_s111_FR0[a_][b_]
                    if w and data["FR"][0][a_][b_]:
                        out[const] += w * data["FR"][0][a_][b_]
            add_cols(core.KG_R, data["FR"])
        else:
            raise ValueError(which)
        return out

    def sos_sum(self, blocks_def, Bblocks: dict) -> list[Fraction]:
        """Σ_r g_r·z_rᵀB_r z_r 的系数向量（blocks_def/self.sosX 之一）。"""
        core = self.core
        ring = core.ring
        out = [F0] * core.nmon
        for name, gnz, mons in blocks_def:
            B = Bblocks[name]
            m = len(mons)
            for p_ in range(m):
                ep = mons[p_]
                row = B[p_]
                for q_ in range(m):
                    c = row[q_]
                    if c == 0:
                        continue
                    eq = mons[q_]
                    base = (ep[0] + eq[0], ep[1] + eq[1], ep[2] + eq[2])
                    for (eg, cg) in gnz:
                        out[ring.index[(base[0] + eg[0], base[1] + eg[1],
                                        base[2] + eg[2])]] += c * cg
        return out

    def minorant_rhs(self, h: list[Fraction]) -> list[Fraction]:
        out = []
        for r in range(self.deg_p + 1):
            out.append(sum(self.Cp[r][j] * h[j] for j in range(self.core.d_H + 1))
                       + self.p_const[r])
        return out

    def minorant_lhs(self, blocks_def, Sblocks: dict) -> list[Fraction]:
        out = [F0] * (self.deg_p + 1)
        for name, mons_y, mult in blocks_def:
            S = Sblocks[name]
            m = len(mons_y)
            for p_ in range(m):
                row = S[p_]
                for q_ in range(m):
                    c = row[q_]
                    if c == 0:
                        continue
                    base = mons_y[p_] + mons_y[q_]
                    for (eg, cg) in mult:
                        out[base + eg] += c * cg
        return out


# ============================================================ 精确自检（组合恒等式 / 正性）
def s_forms(core: TypedCore, Fblocks):
    """s_P、s_R 的系数向量与逐 (k,a,b) 列索引映射。"""
    svecs = [F0, F0]
    svecs = [[F0] * core.nmon, [F0] * core.nmon]
    for k, m_k in enumerate(core.F_sizes):
        for a_ in range(m_k):
            for b_ in range(m_k):
                gi = core.Y_index[(k, a_, b_)]
                for ti, key in enumerate(("FP", "FR")):
                    c = Fblocks[ti][k][a_][b_]
                    if c:
                        svecs[ti] = [x + c * y for x, y in zip(svecs[ti], core.Y_cols[gi])]
    return svecs                                     # [s_P_vec, s_R_vec]


def gm_vec(core: TypedCore, Fmat_list):
    """gm_X 的单变量系数向量（长度 d_H+1，slot0 单项式收集）。"""
    out = [F0] * (core.d_H + 1)
    for k, m_k in enumerate(core.F_sizes):
        for a_ in range(m_k):
            for b_ in range(m_k):
                c = Fmat_list[k][a_][b_]
                if c == 0:
                    continue
                gi = core.Y_index[(k, a_, b_)]
                for p, cc in enumerate(core.gm_cols[gi]):
                    if cc:
                        d = core.ring.mons[p][0]
                        out[d] += c * cc
    return out


def exact_typed_identity_selftest(core: TypedCore, lm: LamMaps, rng, trials=2):
    """组合恒等式：Σ_{i<j}H_cls − e == Σ_T λ_T + Σ_all（随机有理构型，Fraction ==0）。

    λ_T 由数据片段直接求值（不经 lam() 装配），独立验证 share/常数/核簿记；
    另在随机点核对 lam() 装配的系数向量与片段求值一致（验证装配本身）。
    """
    n = core.n
    for _ in range(trials):
        d_H = core.d_H
        data = dict(
            hA=[Fraction(rng.randint(-1 << 12, 1 << 12), 1 << 12) for _ in range(d_H + 1)],
            hB=[Fraction(rng.randint(-1 << 12, 1 << 12), 1 << 12) for _ in range(d_H + 1)],
            hC=[Fraction(rng.randint(-1 << 12, 1 << 12), 1 << 12) for _ in range(d_H + 1)],
            psiBa=[Fraction(rng.randint(-1 << 12, 1 << 12), 1 << 12) for _ in range(d_H + 1)],
            psiCb=[Fraction(rng.randint(-1 << 12, 1 << 12), 1 << 12) for _ in range(d_H + 1)],
            e=Fraction(rng.randint(-1 << 12, 1 << 12), 1 << 12),
            cA=Fraction(rng.randint(-1 << 12, 1 << 12), 1 << 12),
            cB=Fraction(rng.randint(-1 << 12, 1 << 12), 1 << 12))
        data["FP"], data["FR"] = [], []
        for key in ("FP", "FR"):
            lst = []
            for m_k in core.F_sizes:
                G = [[Fraction(rng.randint(-6, 6), 2) for _ in range(m_k)] for _ in range(m_k)]
                Fk = [[sum(G[i][t] * G[j][t] for t in range(m_k)) for j in range(m_k)]
                      for i in range(m_k)]
                lst.append(Fk)
            data[key] = lst
        # c_γ 由计数条件
        sP111 = sum(sum(row) for row in data["FP"][0])
        sR111 = sum(sum(row) for row in data["FR"][0])
        cG = (data["e"] + 2 * sP111 + core.ring_n * sR111
              - core.nPPR * data["cA"] - core.nPRR * data["cB"]) / core.nRRR
        # 随机有理构型（极点 0,1；环 2..n−1）
        X = random_dyadic_config(rng, n)
        G = [[sum(xi[t] * xj[t] for t in range(3)) for xj in X] for xi in X]
        sP_vec, sR_vec = s_forms(core, (data["FP"], data["FR"]))
        gmP, gmR = gm_vec(core, data["FP"]), gm_vec(core, data["FR"])

        def sP(u, v, t):
            return core.eval3(sP_vec, u, v, t)

        def sR(u, v, t):
            return core.eval3(sR_vec, u, v, t)

        def H(vec, x):
            return core.eval1(vec, x)

        # Σ_all（按根分型）
        sall = F0
        for i in range(n):
            f = sP if i < 2 else sR
            for j in range(n):
                for l in range(n):
                    sall += f(G[i][j], G[i][l], G[j][l])
        # Σ_{i<j} H_cls
        sumH = H(data["hA"], G[0][1])
        for r in range(2, n):
            sumH += H(data["hB"], G[0][r]) + H(data["hB"], G[1][r])
        for r in range(2, n):
            for r2 in range(r + 1, n):
                sumH += H(data["hC"], G[r][r2])
        # Σ_T λ_T（片段直接求值）
        lam_sum = F0
        PsiA = [data["hA"][j] - 2 * gmP[j] for j in range(d_H + 1)]
        PsiB = [data["hB"][j] - gmP[j] - gmR[j] for j in range(d_H + 1)]
        wB = [(PsiB[j] - data["psiBa"][j]) * Fraction(1, core.dB) for j in range(d_H + 1)]
        wC = [(data["hC"][j] - 2 * gmR[j] - 2 * data["psiCb"][j]) * Fraction(1, core.dC)
              for j in range(d_H + 1)]
        for r in range(2, n):                                   # PPR {0,1,r}
            u, v, t = G[0][1], G[0][r], G[1][r]
            lam_sum += (H(PsiA, u) * Fraction(1, core.dA) + H(data["psiBa"], v)
                        + H(data["psiBa"], t) - data["cA"]
                        - 2 * (sP(u, v, t) + sP(u, t, v) + sR(v, t, u)))
        for p in (0, 1):                                        # PRR {p,r,r'}
            for r in range(2, n):
                for r2 in range(r + 1, n):
                    u, v, t = G[p][r], G[p][r2], G[r][r2]
                    lam_sum += (H(wB, u) + H(wB, v) + H(data["psiCb"], t) - data["cB"]
                                - 2 * (sP(u, v, t) + sR(u, t, v) + sR(v, t, u)))
        for r in range(2, n):                                   # RRR
            for r2 in range(r + 1, n):
                for r3 in range(r2 + 1, n):
                    u, v, t = G[r][r2], G[r][r3], G[r2][r3]
                    lam_sum += (H(wC, u) + H(wC, v) + H(wC, t) - cG
                                - 2 * (sR(u, v, t) + sR(u, t, v) + sR(v, t, u)))
        lhs = sumH - data["e"]
        rhs = lam_sum + sall
        if lhs != rhs:
            fail(f"精确 typed 组合恒等式自检失败：lhs−rhs = {lhs - rhs} ≠ 0")
        # 装配一致性：lam() 系数向量在随机点 == 片段求值
        for which, pt in (("A", (G[0][1], G[0][2], G[1][2])),
                          ("B", (G[0][2], G[0][3], G[2][3])),
                          ("G", (G[2][3], G[2][4], G[3][4]))):
            vec = lm.lam(which, data)
            u, v, t = pt
            if which == "A":
                direct = (H(PsiA, u) * Fraction(1, core.dA) + H(data["psiBa"], v)
                          + H(data["psiBa"], t) - data["cA"]
                          - 2 * (sP(u, v, t) + sP(u, t, v) + sR(v, t, u)))
            elif which == "B":
                direct = (H(wB, u) + H(wB, v) + H(data["psiCb"], t) - data["cB"]
                          - 2 * (sP(u, v, t) + sR(u, t, v) + sR(v, t, u)))
            else:
                direct = (H(wC, u) + H(wC, v) + H(wC, t) - cG
                          - 2 * (sR(u, v, t) + sR(u, t, v) + sR(v, t, u)))
            if core.eval3(vec, u, v, t) != direct:
                fail(f"λ_{which} 装配与片段求值不一致")
    return dict(trials=trials, exact_zero=True,
                note=(f"ΣH−e == Σ_T λ_T + Σ_all 精确成立（n={core.n}，"
                      f"share 分母 {core.dA}/{core.dB}/{core.dC}，"
                      f"计数 {core.nPPR}/{core.nPRR}/{core.nRRR}）"))


def exact_typed_positivity_selftest(core: TypedCore, rng, trials=2):
    """引理 4.1（typed 版）：逐根 Σ_{j,l}⟨F_type(i),Y_k⟩ ≥ 0 精确成立。"""
    n = core.n
    mins = []
    for _ in range(trials):
        X = random_dyadic_config(rng, n)
        G = [[sum(xi[t] * xj[t] for t in range(3)) for xj in X] for xi in X]
        for i in range(n):
            Fblocks = []
            for m_k in core.F_sizes:
                Gm = [[Fraction(rng.randint(-6, 6), 2) for _ in range(m_k)]
                      for _ in range(m_k)]
                Fblocks.append([[sum(Gm[a][t] * Gm[b][t] for t in range(m_k))
                                 for b in range(m_k)] for a in range(m_k)])
            acc = F0
            for k, m_k in enumerate(core.F_sizes):
                for a_ in range(m_k):
                    for b_ in range(m_k):
                        c = Fblocks[k][a_][b_]
                        if c:
                            gi = core.Y_index[(k, a_, b_)]
                            for j in range(n):
                                for l in range(n):
                                    acc += c * core.eval3(core.Y_cols[gi],
                                                          G[i][j], G[i][l], G[j][l])
            if acc < 0:
                fail(f"typed 正性自检失败：root {i} 的 Σ = {acc} < 0")
            mins.append(float(acc))
    return dict(trials=trials * n, all_nonneg=True, min_float=min(mins))


# ============================================================ SDP 组装（float）
def build_typed_sdp(core: TypedCore, lm: LamMaps):
    sdp_bound.require_cvxpy()
    import cvxpy as cp
    import scipy.sparse as sp

    d_H = core.d_H
    nmon = core.nmon

    hA = cp.Variable(d_H + 1, name="hA")
    hB = cp.Variable(d_H + 1, name="hB")
    hC = cp.Variable(d_H + 1, name="hC")
    psiBa = cp.Variable(d_H + 1, name="psiBa")
    psiCb = cp.Variable(d_H + 1, name="psiCb")
    e = cp.Variable(name="e")
    cA = cp.Variable(name="cA")
    cB = cp.Variable(name="cB")
    FP = [cp.Variable((m, m), symmetric=True, name=f"FP{k}")
          for k, m in enumerate(core.F_sizes)]
    FR = [cp.Variable((m, m), symmetric=True, name=f"FR{k}")
          for k, m in enumerate(core.F_sizes)]

    def fterm(mats_frac, Fvars):
        out = 0
        for k, m_k in enumerate(core.F_sizes):
            A = sp.csr_matrix(core.cols_to_float(mats_frac[k]))
            out = out + A @ cp.vec(Fvars[k], order="C")
        return out

    # F 列按 (k, a,b) 行主序拼接（与 lam() 的 add_cols 索引一致）
    KA_P_cols = list(core.KA_P)
    KA_R_cols = list(core.KA_R)
    KB_P_cols = list(core.KB_P)
    KB_R_cols = list(core.KB_R)
    KG_R_cols = list(core.KG_R)

    def mats_from_cols(cols):
        mats, off = [], 0
        for m_k in core.F_sizes:
            mats.append(cols[off:off + m_k * m_k])
            off += m_k * m_k
        return mats

    def mat_float(Mx):
        return np.array([[float(x) for x in row] for row in Mx])

    def vec_float(v):
        return np.array([float(x) for x in v])

    # λ_Γ 的 s111 附加项：F_P[0]/F_R[0] 全元素和 → 仅落在 const 单项式（(0,0,0)）。
    # 注意必须以"向量 × 标量和"进入：cvxpy 会把标量表达式加法广播到整向量
    # （曾因此给 λ_Γ 的全部非 const 单项式平添一份 s111——被 N7 校准的 R1_G 巨残差抓出）
    s111_vec_P = np.zeros(nmon)
    s111_vec_P[core.ring.index[(0, 0, 0)]] = float(lm.MG_s111_FP0[0][0])
    s111_vec_R = np.zeros(nmon)
    s111_vec_R[core.ring.index[(0, 0, 0)]] = float(lm.MG_s111_FR0[0][0])

    lamA = (mat_float(lm.MA_hA) @ hA + mat_float(lm.MA_psiBa) @ psiBa
            + vec_float(lm.MA_cA) * cA
            + fterm(mats_from_cols(KA_P_cols), FP) + fterm(mats_from_cols(KA_R_cols), FR))
    lamB = (mat_float(lm.MB_hB) @ hB + mat_float(lm.MB_psiBa) @ psiBa
            + mat_float(lm.MB_psiCb) @ psiCb + vec_float(lm.MB_cB) * cB
            + fterm(mats_from_cols(KB_P_cols), FP) + fterm(mats_from_cols(KB_R_cols), FR))
    const111 = (vec_float(lm.MG_e) * e + vec_float(lm.MG_cA) * cA
                + vec_float(lm.MG_cB) * cB
                + s111_vec_P * cp.sum(FP[0])
                + s111_vec_R * cp.sum(FR[0]))
    lamG = (mat_float(lm.MG_hC) @ hC + mat_float(lm.MG_psiCb) @ psiCb
            + const111 + fterm(mats_from_cols(KG_R_cols), FR))

    constraints = [F >> 0 for F in FP] + [F >> 0 for F in FR]

    # SOS 块
    def sos_constraint(blocks_def, lam_expr, tag):
        rhs = cp.Constant(np.zeros(nmon))
        for name, gnz, mons in blocks_def:
            m_ = len(mons)
            rows, cidx, vals = [], [], []
            for p_ in range(m_):
                ep = mons[p_]
                for q_ in range(m_):
                    eq = mons[q_]
                    base = (ep[0] + eq[0], ep[1] + eq[1], ep[2] + eq[2])
                    for (eg, cg) in gnz:
                        ex = (base[0] + eg[0], base[1] + eg[1], base[2] + eg[2])
                        rows.append(core.ring.index[ex])
                        cidx.append(p_ * m_ + q_)
                        vals.append(float(cg))
            A = sp.csr_matrix((vals, (rows, cidx)), shape=(nmon, m_ * m_))
            B = cp.Variable((m_, m_), symmetric=True, name=f"{tag}_{name}")
            constraints.append(B >> 0)
            rhs = rhs + A @ cp.vec(B, order="C")
        constraints.append(rhs == lam_expr)
        return

    sos_constraint(lm.sosA, lamA, "BA")
    sos_constraint(lm.sosB, lamB, "BB")
    sos_constraint(lm.sosG, lamG, "BG")

    # minorant 块
    def minorant_constraint(blocks_def, h, tag):
        rhs = cp.Constant(np.zeros(lm.deg_p + 1))
        for name, mons_y, mult in blocks_def:
            m_ = len(mons_y)
            rows, cidx, vals = [], [], []
            for p_ in range(m_):
                for q_ in range(m_):
                    base = mons_y[p_] + mons_y[q_]
                    for (eg, cg) in mult:
                        rows.append(base + eg)
                        cidx.append(p_ * m_ + q_)
                        vals.append(float(cg))
            A = sp.csr_matrix((vals, (rows, cidx)), shape=(lm.deg_p + 1, m_ * m_))
            B = cp.Variable((m_, m_), symmetric=True, name=f"{tag}_{name}")
            constraints.append(B >> 0)
            rhs = rhs + A @ cp.vec(B, order="C")
        CpF = np.array([[float(x) for x in row] for row in lm.Cp])
        pcF = np.array([float(x) for x in lm.p_const])
        constraints.append(rhs == CpF @ h + pcF)
        return

    minorant_constraint(lm.sig_def, hB, "sigB")
    minorant_constraint(lm.sig_def, hC, "sigC")
    minorant_constraint(lm.tau_def, hA, "tauA")

    prob = cp.Problem(cp.Maximize(e), constraints)
    meta = dict(n=core.n, lo=float(lm.lo), hi=float(lm.hi), M=core.M, K=core.K,
                d_H=d_H, D=core.D, nmon=nmon, F_sizes=core.F_sizes,
                counts=dict(PPR=core.nPPR, PRR=core.nPRR, RRR=core.nRRR,
                            shares=dict(A=core.dA, B=core.dB, C=core.dC)),
                n_scalar_vars=int(sum(v.size for v in prob.variables())),
                n_eq_rows=int(sum(c.size for c in constraints
                                  if not isinstance(c, cp.constraints.PSD))))
    handles = dict(prob=prob, e=e, cA=cA, cB=cB, hA=hA, hB=hB, hC=hC,
                   psiBa=psiBa, psiCb=psiCb, FP=FP, FR=FR)
    return prob, handles, meta


def solution_from_handles(core: TypedCore, V) -> dict:
    def sym(M):
        a = np.asarray(M.value)
        return ((a + a.T) / 2).tolist()

    return dict(
        hA=[float(x) for x in V["hA"].value],
        hB=[float(x) for x in V["hB"].value],
        hC=[float(x) for x in V["hC"].value],
        psiBa=[float(x) for x in V["psiBa"].value],
        psiCb=[float(x) for x in V["psiCb"].value],
        e=float(V["e"].value), cA=float(V["cA"].value), cB=float(V["cB"].value),
        FP=[sym(F) for F in V["FP"]], FR=[sym(F) for F in V["FR"]],
        # SOS / minorant 块由外部传入（solve_slab 附加）
    )


def solve_slab(n, lo: Fraction, hi: Fraction, M, K, verbose=False):
    """数值求解一个 slab 的 typed SDP；返回 (e_val, info, check, sol, core, lm)。"""
    t0 = time.time()
    core = TypedCore(n, M, K)
    lm = LamMaps(core, lo, hi)
    prob, V, meta = build_typed_sdp(core, lm)
    build_s = time.time() - t0
    t1 = time.time()
    import cvxpy as cp
    try:
        prob.solve(solver=cp.CLARABEL, verbose=verbose,
                   max_iter=CFG["SOLVER"]["max_iter"],
                   tol_gap_abs=CFG["SOLVER"]["tol_gap_abs"],
                   tol_gap_rel=CFG["SOLVER"]["tol_gap_rel"],
                   tol_feas=CFG["SOLVER"]["tol_feas"],
                   time_limit=CFG["SOLVER"]["time_limit"])
        solver, status = "CLARABEL", prob.status
    except Exception as exc:
        print(f"[warn] Clarabel 异常（{exc}），SCS 兜底", flush=True)
        prob.solve(solver=cp.SCS, verbose=verbose,
                   eps=CFG["FALLBACK"]["eps"],
                   max_iters=CFG["FALLBACK"]["max_iters"],
                   time_limit_secs=CFG["FALLBACK"]["time_limit_secs"])
        solver, status = "SCS", prob.status
    solve_s = time.time() - t1
    e_val = float(V["e"].value) if V["e"].value is not None else float("nan")
    info = dict(solver=solver, status=status, build_s=round(build_s, 2),
                solve_s=round(solve_s, 2), **meta)
    if status not in ("optimal", "optimal_inaccurate") or V["e"].value is None:
        return e_val, info, None, None, core, lm, V
    sol = solution_from_handles(core, V)
    # 抓 SOS / minorant 块（命名约定与 build_typed_sdp 一致）
    sos_vars = {v.name(): v for v in prob.variables()
                if v.name().startswith(("BA_", "BB_", "BG_", "sigB", "sigC", "tauA"))}
    for nm, var in sos_vars.items():
        a = np.asarray(var.value)
        sol[nm] = ((a + a.T) / 2).tolist()
    check = verify_numerical(core, lm, sol, e_val)
    return e_val, info, check, sol, core, lm, V


def verify_numerical(core: TypedCore, lm: LamMaps, sol: dict, e_val: float):
    """数值复核：3 条 slack 恒等式残差、minorant 残差、PSD 最小特征值、域内 λ 逐点、
    minorant 逐点、指示性 e_safe（正式界由 exact 阶段给出）。"""
    ring = core.ring
    lo_f, hi_f = float(lm.lo), float(lm.hi)

    dataF = {key: [Fraction(x) for x in sol[key]]
             for key in ("hA", "hB", "hC", "psiBa", "psiCb")}
    dataF["e"], dataF["cA"], dataF["cB"] = (Fraction(sol["e"]), Fraction(sol["cA"]),
                                            Fraction(sol["cB"]))
    dataF["FP"] = [[[Fraction(x) for x in row] for row in m] for m in sol["FP"]]
    dataF["FR"] = [[[Fraction(x) for x in row] for row in m] for m in sol["FR"]]

    res = {}
    min_eig = {}
    lams = {}
    for which, blocks_def, prefix in (("A", lm.sosA, "BA"), ("B", lm.sosB, "BB"),
                                      ("G", lm.sosG, "BG")):
        lv = lm.lam(which, dataF)
        sv = lm.sos_sum(blocks_def, {name: [[Fraction(x) for x in row]
                                            for row in sol[f"{prefix}_{name}"]]
                                     for name, _g, _m in blocks_def})
        resid = [x - y for x, y in zip(lv, sv)]
        res[f"R1_{which}"] = sum(abs(x) for x in resid)
        res[f"resid_max_{which}"] = max(abs(x) for x in resid)
        lams[which] = lv
        for name, _g, _m in blocks_def:
            B = np.array(sol[f"{prefix}_{name}"])
            min_eig[f"{prefix}_{name}"] = float(np.linalg.eigvalsh(B).min())
    for nm in ("FP", "FR"):
        for k, m in enumerate(sol[nm]):
            min_eig[f"{nm}{k}"] = float(np.linalg.eigvalsh(np.array(m)).min())
    # minorant 残差与逐点
    R2s = {}
    for X, blocks_def, prefix, hkey in (("A", lm.tau_def, "tauA", "hA"),
                                        ("B", lm.sig_def, "sigB", "hB"),
                                        ("C", lm.sig_def, "sigC", "hC")):
        lhs = lm.minorant_lhs(blocks_def, {name: [[Fraction(x) for x in row]
                                                  for row in sol[f"{prefix}_{name}"]]
                                           for name, _my, _mu in blocks_def})
        rhs = lm.minorant_rhs([Fraction(x) for x in sol[hkey]])
        rr = [x - y for x, y in zip(rhs, lhs)]
        w = lm.w_hat
        R2s[X] = sum(abs(rr[j]) * w ** j for j in range(len(rr)))
        for name, _my, _mu in blocks_def:
            B = np.array(sol[f"{prefix}_{name}"])
            min_eig[f"{prefix}_{name}"] = float(np.linalg.eigvalsh(B).min())
        # 逐点：H ≤ φ 于各自域（粗格点）
        if X == "A":
            tg = np.linspace(lo_f, hi_f, CFG["GRID_NT"] // 4)
        else:
            tg = np.linspace(lo_f, 1.0 - 1e-9, CFG["GRID_NT"] // 4)
        h = np.array(sol[hkey])
        Hv = np.polyval(h[::-1], tg)
        phi = 1.0 / np.sqrt(2.0 - 2.0 * tg)
        res[f"minor_viol_{X}"] = float(np.max(Hv - phi))

    # λ 域内逐点（随机 Gram 三点：box 采样 + detG ≥ 0）
    rng = np.random.default_rng(CFG["SEED"])
    nt = CFG["GRID_NTRIPLE"]
    # λ_A 域：u∈[lo,hi], v,t∈[lo,1]；λ_B/λ_Γ：u,v,t∈[lo,1]
    for tag, dom in (("A", (lo_f, hi_f)), ("B", (lo_f, 1.0)), ("G", (lo_f, 1.0))):
        u = rng.uniform(dom[0], dom[1], nt)
        v = rng.uniform(lo_f, 1.0, nt)
        t = rng.uniform(lo_f, 1.0, nt)
        det = 1 + 2 * u * v * t - u * u - v * v - t * t
        keep = det >= 0
        u, v, t = u[keep], v[keep], t[keep]
        lv = lams[tag]
        vals = np.array([float(x) for x in lv]) @ _vandermonde(core, u, v, t)
        res[f"lam_min_random_{tag}"] = float(vals.min())
        res[f"lam_npts_{tag}"] = int(len(u))
    # 边界族：固定一个槽于切面值 f，另两槽取 detG ≥ 0 的可行段
    # （v,t) 可行 ⟺ t ∈ fv ± √((1−f²)(1−v²))；另含 (x,x,1) 族（detG=(1−x)²(1+2x)）
    def lam_min_faces(tag, faces):
        best = np.inf
        lv = np.array([float(x) for x in lams[tag]])
        # λ_A 的域有上切口 u ≤ hi：采样时必须保持（曾漏掉——面采样在 u>hi 处
        # 合法地为负，误报 accepted=False）
        def keepmask(uu):
            m = ((uu[0] >= lo_f) & (uu[1] >= lo_f) & (uu[2] >= lo_f)
                 & (1 + 2 * uu[0] * uu[1] * uu[2] - uu[0] ** 2
                    - uu[1] ** 2 - uu[2] ** 2 >= -1e-12))
            if tag == "A":
                m &= (uu[0] <= hi_f)
            return m
        for f in faces:
            for slot in range(3):
                gg = np.linspace(lo_f, hi_f if (tag == "A") else 1.0, 4000)
                rge = np.sqrt(max(0.0, 1 - f * f) * (1 - gg * gg))
                free = [i for i in range(3) if i != slot]
                for sgn in (1.0, -1.0):
                    other = f * gg + sgn * rge
                    for arr2 in (other, gg):
                        uu = [None, None, None]
                        uu[slot] = np.full_like(gg, f)
                        uu[free[0]], uu[free[1]] = arr2, gg
                        keep = keepmask(uu)
                        if keep.sum() < 10:
                            continue
                        vals = lv @ _vandermonde(core, uu[0][keep], uu[1][keep],
                                                 uu[2][keep])
                        best = min(best, float(vals.min()))
        lo_xx = max(lo_f, -0.5)
        hi_xx = hi_f if tag == "A" else 1.0
        xx = np.linspace(lo_xx, hi_xx, 2000)              # (x,x,1) 族
        vals = lv @ _vandermonde(core, xx, xx, np.ones_like(xx))
        best = min(best, float(vals.min()))
        return best
    for tag, faces in (("A", (lo_f, hi_f)), ("B", (lo_f,)), ("G", (lo_f,))):
        res[f"lam_min_face_{tag}"] = lam_min_faces(tag, faces)
    # 指示性 e_safe（正式界走 exact 认证；此处给量级）。全部转 float（可 JSON 序列化）
    defl = (core.nPPR * res["R1_A"] + core.nPRR * res["R1_B"] + core.nRRR * res["R1_G"])
    R2max = max(R2s.values())
    res["indicative_deflation"] = float(defl)
    res["R2_max"] = float(R2max)
    res["e_safe_indicative"] = float((Fraction(sol["e"]) - defl) / (1 + R2max))
    res["R2s"] = {k: float(v) for k, v in R2s.items()}
    for w in "ABG":
        res[f"R1_{w}"] = float(res[f"R1_{w}"])
        res[f"resid_max_{w}"] = float(res[f"resid_max_{w}"])
    res["min_eig"] = min_eig
    acc = CFG["ACCEPT"]
    res["accepted"] = bool(
        max(res[f"resid_max_{w}"] for w in "ABG") <= acc["identity_residual"]
        and min(res[f"lam_min_random_{w}"] for w in "ABG") >= acc["slack_min"]
        and min(v for k, v in res.items() if k.startswith("lam_min_face")) >= acc["slack_min"]
        and min(min_eig.values()) >= acc["min_eig"]
        and max(res[f"minor_viol_{X}"] for X in "ABC") <= 1e-6)
    return res


def _vandermonde(core, u, v, t):
    """nmon × npts 的单项式值矩阵（与 ring.mons 同序）。"""
    u, v, t = np.asarray(u), np.asarray(v), np.asarray(t)
    cols = [np.ones_like(u)]
    D = core.D
    pw_u = [np.ones_like(u)] + [None] * D
    pw_v = [np.ones_like(u)] + [None] * D
    pw_t = [np.ones_like(u)] + [None] * D
    for i in range(1, D + 1):
        pw_u[i] = pw_u[i - 1] * u
        pw_v[i] = pw_v[i - 1] * v
        pw_t[i] = pw_t[i - 1] * t
    M = np.empty((core.nmon, len(u)))
    for p, (i, j, l) in enumerate(core.ring.mons):
        M[p] = pw_u[i] * pw_v[j] * pw_t[l]
    return M


# ============================================================ exact 认证
def ceil_sqrt_rat(x: Fraction) -> Fraction:
    p, q = x.numerator, x.denominator
    return Fraction(math.isqrt(p * q) + 1, q)


def certify_slab(core: TypedCore, lm: LamMaps, sol: dict, k: int,
                 E_star: Fraction, slab_tag: str):
    """一个 dyadic 粒度上的完整认证链；断言失败 fail()。返回证书数据与精确界。"""
    t0 = time.time()
    d_H = core.d_H

    def rround(x):
        return dyad(float(x), k)

    data_dy = dict(
        hA=[rround(x) for x in sol["hA"]], hB=[rround(x) for x in sol["hB"]],
        hC=[rround(x) for x in sol["hC"]],
        psiBa=[rround(x) for x in sol["psiBa"]], psiCb=[rround(x) for x in sol["psiCb"]],
        e=dyad(float(sol["e"]), k, floor=True),
        cA=rround(sol["cA"]), cB=rround(sol["cB"]))

    shifts = {}
    F_dy = {}
    for nm in ("FP", "FR"):
        F_dy[nm] = []
        for kk, m_k in enumerate(core.F_sizes):
            Mfr = [[rround(x) for x in row] for row in sol[nm][kk]]
            Mfr, d, tries = repair_psd(f"{nm}{kk}", Mfr, k)
            shifts[f"{nm}{kk}"] = d
            F_dy[nm].append(Mfr)
    data_dy["FP"], data_dy["FR"] = F_dy["FP"], F_dy["FR"]

    sos_dy = {}
    for which, blocks_def, prefix in (("A", lm.sosA, "BA"), ("B", lm.sosB, "BB"),
                                      ("G", lm.sosG, "BG")):
        sos_dy[which] = {}
        for name, _g, _m in blocks_def:
            Mfr = [[rround(x) for x in row] for row in sol[f"{prefix}_{name}"]]
            Mfr, d, tries = repair_psd(f"{prefix}_{name}", Mfr, k)
            shifts[f"{prefix}_{name}"] = d
            sos_dy[which][name] = Mfr
    mino_dy = {}
    for X, blocks_def, prefix in (("A", lm.tau_def, "tauA"), ("B", lm.sig_def, "sigB"),
                                  ("C", lm.sig_def, "sigC")):
        mino_dy[X] = {}
        for name, _my, _mu in blocks_def:
            Mfr = [[rround(x) for x in row] for row in sol[f"{prefix}_{name}"]]
            Mfr, d, tries = repair_psd(f"{prefix}_{name}", Mfr, k)
            shifts[f"{prefix}_{name}"] = d
            mino_dy[X][name] = Mfr

    # ---- 精确残差 ----
    R1 = {}
    for which, blocks_def in (("A", lm.sosA), ("B", lm.sosB), ("G", lm.sosG)):
        lv = lm.lam(which, data_dy)
        sv = lm.sos_sum(blocks_def, sos_dy[which])
        resid = [x - y for x, y in zip(lv, sv)]
        R1[which] = sum(abs(x) for x in resid)
    R2 = {}
    for X, blocks_def in (("A", lm.tau_def), ("B", lm.sig_def), ("C", lm.sig_def)):
        lhs = lm.minorant_lhs(blocks_def, mino_dy[X])
        hkey = {"A": "hA", "B": "hB", "C": "hC"}[X]
        rhs = lm.minorant_rhs(data_dy[hkey])
        rr = [x - y for x, y in zip(rhs, lhs)]
        w = lm.w_hat
        R2[X] = sum(abs(rr[j]) * w ** j for j in range(len(rr)))

    e_dy = data_dy["e"]
    defl = core.nPPR * R1["A"] + core.nPRR * R1["B"] + core.nRRR * R1["G"]
    R2max = max(R2.values())
    if e_dy - defl <= 0:
        fail(f"[{slab_tag}] e − 膨胀 = {e_dy - defl} ≤ 0")
    certified = (e_dy - defl) / (1 + R2max)

    # ---- 逐点抽查（有理 (u,v,t) 直接采样：域条件 = detG ≥ 0 ＋切口/上界，----
    # ---- 不需要可实现性——SOS 机制只在域上用 g_r ≥ 0 与 |单项式| ≤ 1）。 ----
    rng = random.Random(97531 + k + hash(slab_tag) % 1000)
    spot = {}
    lam_vecs = {which: lm.lam(which, data_dy) for which in "ABG"}
    for which, blocks_def in (("A", lm.sosA), ("B", lm.sosB), ("G", lm.sosG)):
        u_ok = 0
        tries = 0
        while tries < 200 and u_ok < 8:
            tries += 1
            lo, hi = lm.lo, lm.hi
            # u：λ_A 的最小对内积窗口 [lo,hi]，B/G 取 [lo,1]；
            # 用随机有理数直接采样（窄窗也不迷路——曾用随机球面点采样，
            # [−0.97,−0.95] 窗 60 次取不到点）
            def rq(a, b):
                return a + (b - a) * Fraction(rng.randint(0, 64), 64)
            u = rq(lo, hi if which == "A" else F1)
            v = rq(lo, F1)
            t = rq(lo, F1)
            detg = F1 + 2 * u * v * t - u * u - v * v - t * t
            if detg < 0:
                continue
            u_ok += 1
            lam_pt = core.eval3(lam_vecs[which], u, v, t)
            sos_pt = F0
            for name, gnz, mons in blocks_def:
                B = sos_dy[which][name]
                m = len(mons)
                zp = [(u ** e2[0]) * (v ** e2[1]) * (t ** e2[2]) for e2 in mons]
                quad = sum(B[p][q] * zp[p] * zp[q] for p in range(m) for q in range(m))
                g = sum(c * (u ** eg[0]) * (v ** eg[1]) * (t ** eg[2]) for eg, c in gnz)
                if g < 0:
                    fail(f"[{slab_tag}] 抽查乘子负值：g_{name} = {g} < 0")
                sos_pt += g * quad
            if sos_pt < 0:
                fail(f"[{slab_tag}] SOS 抽查负值（λ_{which}）")
            if lam_pt + R1[which] < 0:
                fail(f"[{slab_tag}] λ_{which} 抽查 < −R1：{lam_pt} < {-R1[which]}")
        if u_ok == 0:
            fail(f"[{slab_tag}] λ_{which} 抽查未取到域内点")
        spot[f"lam{which}"] = dict(checked=u_ok, all_ok=True)
    # minorant 抽查：(2−2t)·H² ≤ (1+R2_X)² 于各自域的有理点
    for X, (lo_, hi_), hkey in (("A", (lm.lo, lm.hi), "hA"), ("B", (lm.lo, F1), "hB"),
                                ("C", (lm.lo, F1), "hC")):
        R2X = R2[X]
        pts = [lo_, (lo_ + hi_) / 2, hi_ if X == "A" else Fraction(9, 10),
               Fraction(-1, 2) if lo_ <= Fraction(-1, 2) else lo_,
               Fraction(-3, 4) if lo_ <= Fraction(-3, 4) else lo_,
               Fraction(0), Fraction(1, 4), Fraction(1, 2), Fraction(3, 4),
               Fraction(995, 1000)]
        for t in pts:
            if not (lo_ <= t < 1):
                continue
            # H_A 的认证域是 [lo,hi]（τ 双侧块 [c,b]；文件头 "H_A ≤ φ 于 [lo,hi]"）：
            # hi 之外的点不受证书约束，抽查须限制在域内——2026-10-05 条带 (8,6) 解的
            # H_A 在 t=0.5 处合法超过 φ，旧抽查（只过滤 t<1）会把有效证书误判失败
            if X == "A" and t > hi_:
                continue
            Ht = core.eval1(data_dy[hkey], t)
            if Ht <= 0:
                continue
            if (2 - 2 * t) * Ht * Ht > (1 + R2X) ** 2:
                fail(f"[{slab_tag}] minorant {X} 抽查失败 @t={float(t)}")
        spot[f"minor{X}"] = dict(all_ok=True)

    # ---- 断言：正裕度（本任务核心）与 sanity ----
    e_fl = float(sol["e"])
    if not certified > E_star:
        fail(f"[{slab_tag}] certified = {float(certified):.12f} ≤ E* = {float(E_star):.9f}"
             f"（正裕度断言失败，粒度 2^-{k}）")
    if certified > Fraction(sol["e"]) + Fraction(1, 10 ** 9):
        fail(f"[{slab_tag}] certified {float(certified):.12f} > 数值 e {e_fl:.12f}"
             f"+1e-9（不可能：舍入只损失）")
    print(f"[{slab_tag}] certified = {float(certified):.12f} > E*（正裕度 "
          f"{float(certified - E_star):.3e}）✓；defl={float(defl):.3e}，"
          f"R2max={float(R2max):.3e}（粒度 2^-{k}，认证链 {time.time() - t0:.0f}s）",
          flush=True)
    return dict(data=data_dy, sos=sos_dy, mino=mino_dy, shifts=shifts,
                R1={w: R1[w] for w in "ABG"}, R2={X: R2[X] for X in "ABC"},
                deflation=defl, R2max=R2max, certified=certified, spot=spot, k=k)


def write_slab_certificate(core: TypedCore, lm: LamMaps, cert_data: dict,
                           E_star: Fraction, slab_tag: str, sol: dict, info: dict,
                           check, src_desc: str, out_path: Path):
    d_H = core.d_H
    data = cert_data["data"]
    blocks = {"e": [[fraction_to_str(data["e"])]],
              "cA": [[fraction_to_str(data["cA"])]],
              "cB": [[fraction_to_str(data["cB"])]],
              "cG": [[fraction_to_str(c_gamma(core, data))]]}
    for key in ("hA", "hB", "hC", "psiBa", "psiCb"):
        blocks[f"{key}_diag"] = [[fraction_to_str(data[key][j]) if i == j else "0"
                                  for j in range(d_H + 1)] for i in range(d_H + 1)]
    for nm in ("FP", "FR"):
        for kk in range(core.K):
            blocks[f"{nm}{kk}"] = [[fraction_to_str(x) for x in row]
                                   for row in data[nm][kk]]
    for which, blocks_def, prefix in (("A", lm.sosA, "BA"), ("B", lm.sosB, "BB"),
                                      ("G", lm.sosG, "BG")):
        for name, _g, _m in blocks_def:
            blocks[f"{prefix}_{name}"] = [[fraction_to_str(x) for x in row]
                                          for row in cert_data["sos"][which][name]]
    for X, blocks_def, prefix in (("A", lm.tau_def, "tauA"), ("B", lm.sig_def, "sigB"),
                                  ("C", lm.sig_def, "sigC")):
        for name, _my, _mu in blocks_def:
            blocks[f"{prefix}_{name}"] = [[fraction_to_str(x) for x in row]
                                          for row in cert_data["mino"][X][name]]
    certified = cert_data["certified"]
    prov = {
        "repo": "thomson-n9",
        "generator": f"numerics/bounds/slab_band.py（{src_desc}）",
        "date": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "upstream": ("typed 三点界自 N=7 证明移植：references/thomson-n7-lean/paper/"
                     "PAPER.md §6–7.1（极点/环分型、share、λ_A/B/Γ、计数条件 (6)、"
                     "slab 域 §6.4）；核/引理 4.1 同 §4；exact.py LDLᵀ＋schema.py 交接"),
        "params": {
            "N": core.n, "M": core.M, "K": core.K, "d_H": d_H, "D": core.D,
            "nmon": core.nmon, "F_sizes": core.F_sizes,
            "m_lo": fraction_to_str(lm.lo), "m_hi": fraction_to_str(lm.hi),
            "b2": fraction_to_str(lm.b2), "c2": fraction_to_str(lm.c2),
            "w_hat": fraction_to_str(lm.w_hat), "round_bits": cert_data["k"],
            "counts": dict(PPR=core.nPPR, PRR=core.nPRR, RRR=core.nRRR,
                           pairA=1, pairB=2 * core.ring_n,
                           pairC=core.ring_n * (core.ring_n - 1) // 2),
            "shares": (f"pair A @ring ×{core.dA}：Ψ_A/{core.dA}；pair B @pole ψ_Ba、"
                       f"@ring ×{core.dB}：(Ψ_B−ψ_Ba)/{core.dB}；pair C @pole ×2 ψ_Cb、"
                       f"@ring ×{core.dC}：(Ψ_C−2ψ_Cb)/{core.dC}"),
            "constant_condition": (f"{core.nPPR}·c_α+{core.nPRR}·c_β+{core.nRRR}·c_γ "
                                   f"= e + 2·s_P(1,1,1) + {core.ring_n}·s_R(1,1,1)"),
            "scope": (f"对一切可重排使 (0,1) 为最小内积对且 m = ⟨x_0,x_1⟩ ∈ "
                      f"[{fraction_to_str(lm.lo)}, {fraction_to_str(lm.hi)}] 的 "
                      f"{core.n} 点单位球面构型，E(x) ≥ claimed_bound。"
                      f"候选 TTP（m* = −0.7475605）不在域内——正裕度的来源"),
            "blocks_map": ("e/cA/cB/cG＝标量；hA/hB/hC/psiBa/psiCb_diag 对角线＝多项式"
                           "系数（t^0..t^d_H）；FP0..FP{K-1}/FR0..FR{K-1}＝F 块；"
                           "BA_/BB_/BG_＋乘子名＝λ SOS Gram（乘子 1,u−lo,v−lo,t−lo,"
                           "hi-u(仅 A),detG，单项式表由 D 定）；tauA_/sigB_/sigC_＝"
                           "minorant Lukács 块（H_A 双侧 [c,b]，H_B/H_C 单侧 [0,b]）"),
            "bound_formula": (
                "certified = (e − (nPPR·R1_A + nPRR·R1_B + nRRR·R1_Γ)) / (1 + R2_max)。"
                "推导：typed 组合恒等式 Σ_{i<j}H_cls − e = Σ_T λ_T + Σ_all（精确自检）；"
                "Σ_all ≥ 0（F ⪰ 0 LDLᵀ 已验 ＋ 引理 4.1 逐根正性）；λ_X ≥ −R1_X 于域"
                "（SOS ≥ 0 ＋ |resid| ≤ ‖resid‖₁，|u|,|v|,|t| ≤ 1）⇒ ΣH ≥ e − 膨胀；"
                "1−2yH_X(1−2y²) ≥ −R2_X 于 y 域（块 ⪰ 0）⇒ H_X ≤ (1+R2_max)·φ ⇒ "
                "E = Σφ ≥ ΣH/(1+R2_max) ≥ certified"),
            "R1": {w: fraction_to_str(cert_data["R1"][w]) for w in "ABG"},
            "R2": {X: fraction_to_str(cert_data["R2"][X]) for X in "ABC"},
            "deflation_exact": fraction_to_str(cert_data["deflation"]),
            "R2max_exact": fraction_to_str(cert_data["R2max"]),
            "psd_shifts": {nm: fraction_to_str(d) for nm, d in cert_data["shifts"].items()},
        },
        "numerical_bound": {"e_raw": sol.get("e"), "status": info.get("status"),
                            "solver": info.get("solver"),
                            "e_safe_indicative": (check or {}).get("e_safe_indicative")},
        "exact_bound": fraction_to_str(certified),
        "margin_over_E_star": fraction_to_str(certified - E_star),
        "checks": {
            "exact_typed_combination_identity_random_rational": True,
            "exact_lemma4_1_typed_positivity_random_rational": True,
            "all_blocks_exact_ldlt_positive_definite": True,
            "lam_spot_checks_domain": cert_data["spot"],
            "certified_gt_E_star_positive_margin": True,
            "readback_recompute_bitwise": True,
        },
        "repro": (f"numerics/.venv/bin/python numerics/bounds/slab_band.py "
                  f"--slabs \"{fraction_to_str(lm.lo)}:{fraction_to_str(lm.hi)}\""),
    }
    cert_obj = Certificate(m_lo=fraction_to_str(lm.lo), m_hi=fraction_to_str(lm.hi),
                           blocks=blocks, claimed_bound=fraction_to_str(certified),
                           provenance=prov)
    text = encode_certificate(cert_obj)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(text)
    # 回读重算
    rt = decode_certificate(out_path.read_text())
    rt_core, rt_lm = rebuild_from_params(rt)
    rt_certified = recompute_certified(rt_core, rt_lm, rt)
    if rt_certified != certified:
        fail(f"[{slab_tag}] 回读重算不一致：{rt_certified} ≠ {certified}")
    if encode_certificate(rt) != text:
        fail(f"[{slab_tag}] 回读再编码不逐字节一致")
    # 全块 LDLᵀ（进程内；进程外复核走 --verify-cert）
    for name, mat in rt.blocks.items():
        if name.endswith("_diag") or name in ("e", "cA", "cB", "cG"):
            continue
        if not is_positive_definite([[Fraction(x) for x in row] for row in mat]):
            fail(f"[{slab_tag}] 块 {name} LDLᵀ 非正定")
    print(f"[{slab_tag}] 证书写入 {out_path.relative_to(REPO)}（{len(text)} 字节）；"
          f"回读重算逐位一致 ✓ 全块 LDLᵀ ✓", flush=True)
    return out_path


def c_gamma(core: TypedCore, data: dict) -> Fraction:
    sP111 = sum(sum(row) for row in data["FP"][0])
    sR111 = sum(sum(row) for row in data["FR"][0])
    return (data["e"] + 2 * sP111 + core.ring_n * sR111
            - core.nPPR * data["cA"] - core.nPRR * data["cB"]) / core.nRRR


def rebuild_from_params(rt) -> tuple[TypedCore, LamMaps]:
    p = rt.provenance["params"]
    core = TypedCore(int(p["N"]), int(p["M"]), int(p["K"]))
    lm = LamMaps(core, Fraction(rt.m_lo), Fraction(rt.m_hi))
    return core, lm


def recompute_certified(core: TypedCore, lm: LamMaps, rt) -> Fraction:
    """从证书 JSON 的块独立重算 certified（验证器可独立实现同一公式）。"""
    d_H = core.d_H
    data = dict(
        hA=[Fraction(rt.blocks["hA_diag"][j][j]) for j in range(d_H + 1)],
        hB=[Fraction(rt.blocks["hB_diag"][j][j]) for j in range(d_H + 1)],
        hC=[Fraction(rt.blocks["hC_diag"][j][j]) for j in range(d_H + 1)],
        psiBa=[Fraction(rt.blocks["psiBa_diag"][j][j]) for j in range(d_H + 1)],
        psiCb=[Fraction(rt.blocks["psiCb_diag"][j][j]) for j in range(d_H + 1)],
        e=Fraction(rt.blocks["e"][0][0]), cA=Fraction(rt.blocks["cA"][0][0]),
        cB=Fraction(rt.blocks["cB"][0][0]))
    data["cG"] = Fraction(rt.blocks["cG"][0][0])
    data["FP"] = [[[Fraction(x) for x in row] for row in rt.blocks[f"FP{k}"]]
                  for k in range(core.K)]
    data["FR"] = [[[Fraction(x) for x in row] for row in rt.blocks[f"FR{k}"]]
                  for k in range(core.K)]
    # cG 一致性（计数条件）
    if data["cG"] != c_gamma(core, data):
        raise ValueError("cG 与计数条件不一致")
    R1 = {}
    for which, blocks_def, prefix in (("A", lm.sosA, "BA"), ("B", lm.sosB, "BB"),
                                      ("G", lm.sosG, "BG")):
        lv = lm.lam(which, data)
        sv = lm.sos_sum(blocks_def,
                        {name: [[Fraction(x) for x in row]
                                for row in rt.blocks[f"{prefix}_{name}"]]
                         for name, _g, _m in blocks_def})
        R1[which] = sum(abs(x - y) for x, y in zip(lv, sv))
    R2 = {}
    for X, blocks_def, prefix, hkey in (("A", lm.tau_def, "tauA", "hA"),
                                        ("B", lm.sig_def, "sigB", "hB"),
                                        ("C", lm.sig_def, "sigC", "hC")):
        lhs = lm.minorant_lhs(blocks_def,
                              {name: [[Fraction(x) for x in row]
                                      for row in rt.blocks[f"{prefix}_{name}"]]
                               for name, _my, _mu in blocks_def})
        rhs = lm.minorant_rhs(data[hkey])
        rr = [x - y for x, y in zip(rhs, lhs)]
        w = lm.w_hat
        R2[X] = sum(abs(rr[j]) * w ** j for j in range(len(rr)))
    defl = core.nPPR * R1["A"] + core.nPRR * R1["B"] + core.nRRR * R1["G"]
    return (data["e"] - defl) / (1 + max(R2.values()))


def verify_cert_file(path: Path, E_star: Fraction):
    """进程外独立复核：只读证书 JSON——结构重建、cG 计数条件、全块 LDLᵀ、
    界值重算逐位比对、正裕度断言。"""
    rt = decode_certificate(path.read_text())
    core, lm = rebuild_from_params(rt)
    # 全块 LDLᵀ
    n_psd = 0
    for name, mat in rt.blocks.items():
        if name.endswith("_diag") or name in ("e", "cA", "cB", "cG"):
            continue
        if not is_positive_definite([[Fraction(x) for x in row] for row in mat]):
            fail(f"[verify] 块 {name} LDLᵀ 非正定")
        n_psd += 1
    cert2 = recompute_certified(core, lm, rt)
    claimed = Fraction(rt.claimed_bound)
    if cert2 != claimed:
        fail(f"[verify] 界值重算 {cert2} ≠ 声称 {claimed}")
    if not claimed > E_star:
        fail(f"[verify] claimed {float(claimed):.12f} ≤ E*（正裕度断言失败）")
    print(f"[verify] {path.name}：{n_psd} 块 LDLᵀ 正定 ✓；界值重算逐位一致 ✓；"
          f"claimed = {float(claimed):.12f} > E*（裕度 {float(claimed - E_star):.3e}）✓",
          flush=True)
    return dict(file=str(path), n_psd_blocks=n_psd,
                claimed=fraction_to_str(claimed), recomputed=fraction_to_str(cert2),
                margin=float(claimed - E_star))


# ============================================================ 主流程
def parse_slabs(spec: str):
    out = []
    for part in spec.split(","):
        lo_s, hi_s = part.split(":")
        out.append((Fraction(lo_s), Fraction(hi_s)))
    return out


def slab_tag(lo: Fraction, hi: Fraction) -> str:
    def f(x):
        s = fraction_to_str(x)
        return s.replace("/", "o").replace("-", "m")
    return f"s{f(lo)}_{f(hi)}"


def main() -> None:
    ap = argparse.ArgumentParser(description="N=9 slab 带 typed 三点证书")
    ap.add_argument("--slabs", type=str, default=None,
                    help='逗号分隔的 "lo:hi"（有理数），如 "-1:-99/100,-99/100:-97/100"')
    ap.add_argument("--config", choices=list(CFG["CONFIGS"]), default=CFG["DEFAULT_CONFIG"])
    ap.add_argument("--n7config", action="store_true", help="用 N7 的 (6,6) 配置（校准用）")
    ap.add_argument("--k", type=int, nargs="+", default=CFG["K_LIST"])
    ap.add_argument("--selftest", action="store_true", help="只跑精确自检（无需 cvxpy）")
    ap.add_argument("--calib7", action="store_true", help="N=7 slab 校准")
    ap.add_argument("--solve-only", action="store_true")
    ap.add_argument("--solution", type=str, default=None,
                    help="复用解数据 JSON（跳过求解）")
    ap.add_argument("--verify-cert", type=str, default=None,
                    help="独立复核一份证书 JSON（只读该文件）")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    E_star, E_src = load_E_star()

    if args.verify_cert:
        verify_cert_file(Path(args.verify_cert), E_star)
        return

    if args.selftest:
        rng = random.Random(CFG["SEED"])
        M, K = CFG["CONFIGS"][args.config]
        core = TypedCore(CFG["N"], M, K)
        lm = LamMaps(core, Fraction(-1), Fraction(-99, 100))
        print(f"[selftest] N={CFG['N']} (M,K)=({M},{K}) D={core.D} "
              f"nmon={core.nmon}", flush=True)
        r1 = exact_typed_identity_selftest(core, lm, rng)
        r2 = exact_typed_positivity_selftest(core, rng)
        print(f"[selftest] 组合恒等式：{json.dumps(r1, ensure_ascii=False)}", flush=True)
        print(f"[selftest] typed 正性：{json.dumps(r2, ensure_ascii=False)}", flush=True)
        return

    if args.calib7:
        cal = CFG["CALIB7"]
        M, K = CFG["N7CONFIG"]
        print(f"[calib7] N=7 slab [{float(cal['lo'])},{float(cal['hi'])}] (M,K)=({M},{K})"
              f"，期望 e ≈ {cal['expect']}（N7 论文 slab 1 的 E(P)+2.5858e-6）", flush=True)
        e_val, info, chk, sol, core, lm, V = solve_slab(
            7, cal["lo"], cal["hi"], M, K, verbose=args.verbose)
        print(f"[calib7] e = {e_val!r}（{info['solver']} {info['status']}，"
              f"{info['build_s']}s+{info['solve_s']}s）", flush=True)
        if chk:
            print(f"[calib7] 复核 R1 = "
                  f"{ {w: float(chk[f'R1_{w}']) for w in 'ABG'} }，"
                  f"e_safe_ind = {chk['e_safe_indicative']:.9f}", flush=True)
        ep = float(N7_ESTAR)
        diff = e_val - cal["expect"]
        # 方向性判据：N7 的 slab-1 证书（e=E(P)+2.5858e-6）是本松弛的可行点
        # （同 6/5/5 SOS 布局、同 minorant 模族），故本 SDP 最优 e ≥ N7 值 − 容差；
        # 高出属正常（N7 对五片用了同一个保守 e，本处逐片取最优）。过高（> tol）
        # 则提示模族/装配有错。另要求正裕度 e > E(P)。
        ok = bool(e_val > ep and e_val >= cal["expect"] - 1e-6
                  and abs(diff) <= cal["tol"] and chk and chk["accepted"])
        print(f"[calib7] {'OK' if ok else 'MISMATCH'}：e − E(P) = {e_val - ep:.3e}"
              f"（正裕度），e − N7 值 = {diff:+.3e}（应为 ≥0 的小量）", flush=True)
        if not ok:
            sys.exit(1)
        return

    # ---- slab 主流程 ----
    if args.slabs:
        slabs = parse_slabs(args.slabs)
    else:
        eps = CFG["DEFAULT_SLABS"]
        slabs = [(eps[i], eps[i + 1]) for i in range(len(eps) - 1)]
    M, K = (CFG["N7CONFIG"] if args.n7config else CFG["CONFIGS"][args.config])

    results_path = HERE / "results" / "slab_band.json"
    results = {"kind": "slab_band", "script": "slab_band.py",
               "timestamp": datetime.now(timezone.utc).isoformat(timespec="seconds"),
               "seed": CFG["SEED"], "E_star": float(E_star), "E_star_src": E_src,
               "config": args.config, "M": M, "K": K,
               "method": ("typed 三点界（N7 PAPER.md §6 移植）：极点=最小对+环分型，"
                          "λ_A/B/Γ SOS＋双侧/单侧 minorant，Clarabel 求→dyadic 舍入→"
                          "LDLᵀ＋精确残差折减"),
               "slabs": []}
    if results_path.exists():
        try:
            old = json.load(open(results_path))
            if old.get("config") == args.config:
                results["slabs"] = [
                    s for s in old.get("slabs", [])
                    if (Fraction(s["m_lo"]), Fraction(s["m_hi"])) not in slabs]
                results["note_merged"] = ("同 config 复跑：同 slab 覆盖，"
                                          f"历史 {len(old.get('slabs', []))} 条中保留 "
                                          f"{len(results['slabs'])} 条")
        except Exception:
            pass

    rng = random.Random(CFG["SEED"])
    sol_dir = HERE / "results"
    for lo, hi in slabs:
        tag = slab_tag(lo, hi)
        print(f"\n[slab {tag}] N=9 [{fraction_to_str(lo)}, {fraction_to_str(hi)}] "
              f"(M,K)=({M},{K})", flush=True)
        sol_path = sol_dir / f"slab_sol_{tag}_{args.config}.json"
        if args.solution:
            with open(args.solution) as f:
                sol = json.load(f)
            src_desc = f"复用解数据 {args.solution}"
        elif args.solve_only is False and sdp_bound.cp is None:
            if not sol_path.exists():
                fail(f"无 cvxpy 且无解数据 {sol_path}")
            with open(sol_path) as f:
                sol = json.load(f)
            src_desc = f"回退已落盘解数据 {sol_path.relative_to(REPO)}"
        else:
            e_val, info, chk, sol, core, lm, V = solve_slab(
                CFG["N"], lo, hi, M, K, verbose=args.verbose)
            info = dict(info)
            info.pop("F_sizes", None)
            print(f"[slab {tag}] e = {e_val!r}（{info['solver']} {info['status']}，"
                  f"{info['build_s']}s 构建 + {info['solve_s']}s 求解）", flush=True)
            if chk:
                print(f"[slab {tag}] 复核：R1_A/B/G = "
                      f"{float(chk['R1_A']):.2e}/{float(chk['R1_B']):.2e}/"
                      f"{float(chk['R1_G']):.2e}；λ_min = "
                      f"{min(chk[f'lam_min_random_{w}'] for w in 'ABG'):.2e}；"
                      f"e_safe_ind = {chk['e_safe_indicative']:.9f}；"
                      f"accepted = {chk['accepted']}", flush=True)
            sol = dict(sol)
            sol["_solver_info"] = info
            sol["_verify"] = chk
            sol_path.parent.mkdir(parents=True, exist_ok=True)
            sol_path.write_text(json.dumps(sol, ensure_ascii=False))
            src_desc = (f"本次求解（Clarabel/SCS，解数据存 "
                        f"{sol_path.relative_to(REPO)}）")
            if args.solve_only:
                entry = dict(slab=tag, m_lo=fraction_to_str(lo), m_hi=fraction_to_str(hi),
                             e_raw=e_val, status=info.get("status"),
                             e_safe_indicative=(chk or {}).get("e_safe_indicative"),
                             solve_s=info.get("solve_s"))
                results["slabs"].append(entry)
                continue
        # 认证（粒度依次尝试）
        core = TypedCore(CFG["N"], M, K)
        lm = LamMaps(core, lo, hi)
        id_chk = exact_typed_identity_selftest(core, lm, rng, trials=1)
        pos_chk = exact_typed_positivity_selftest(core, rng, trials=1)
        print(f"[slab {tag}] 精确自检：组合恒等式 ==0 ✓；typed 正性 ≥0 ✓", flush=True)
        cert_data = None
        last = None
        for k in args.k:
            try:
                cert_data = certify_slab(core, lm, sol, k, E_star, tag)
            except SystemExit as exc:
                last = exc.code
                print(f"[retry {tag}] 粒度 2^-{k} 未过断言，换更细粒度", flush=True)
                continue
            break
        if cert_data is None:
            results["slabs"].append(dict(
                slab=tag, m_lo=fraction_to_str(lo), m_hi=fraction_to_str(hi),
                certified=None, status="CERTIFY_FAILED"))
            dump(results, results_path)
            fail(f"[{tag}] 全部粒度 {args.k} 均未通过断言（最后失败码 {last}）")
        out_path = REPO / "certificates" / f"n9-stage-a2-slab-{tag}.json"
        write_slab_certificate(core, lm, cert_data, E_star, tag, sol,
                               sol.get("_solver_info", {}), sol.get("_verify"),
                               src_desc, out_path)
        margin = cert_data["certified"] - E_star
        entry = dict(
            slab=tag, m_lo=fraction_to_str(lo), m_hi=fraction_to_str(hi),
            bound=fraction_to_str(cert_data["certified"]),
            bound_float=float(cert_data["certified"]),
            margin=fraction_to_str(margin), margin_float=float(margin),
            e_raw=sol.get("e"),
            deflation=float(cert_data["deflation"]),
            R1={w: float(cert_data["R1"][w]) for w in "ABG"},
            R2={X: float(cert_data["R2"][X]) for X in "ABC"},
            round_bits=cert_data["k"],
            certificate=str(out_path.relative_to(REPO)),
            solver_info=sol.get("_solver_info"),
            status="CERTIFIED")
        results["slabs"].append(entry)
        dump(results, results_path)
        # 进程内顺手独立复核（同代码路径；--verify-cert 供进程外）
    dump(results, results_path)
    print(f"\n[done] {len(results['slabs'])} 片处理完毕，结果 {results_path.relative_to(REPO)}",
          flush=True)


def dump(results, out_path):
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(results, f, ensure_ascii=False, indent=2)
    print(f"[out] 已写入 {out_path}", flush=True)


if __name__ == "__main__":
    main()
