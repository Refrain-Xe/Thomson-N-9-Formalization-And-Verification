#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""sdp_certify.py — 三点 SDP 下界（midlarge, m=−0.90）的数值→精确桥接（dyadic 舍入＋纯 Fractions 重算）。

把 Round 1 的 SDP 数值界 e_safe = 25.752724581（results/sdp.json，m=−0.90 ×
midlarge=(8,6)，主界来源；small 配置对求解器有 ~1e-4 依赖，不用）严格化为
**精确 dyadic 有理数证书**。方法对齐 verify_certificate.py（LP 桥）的四步模式，
但 SDP 的两条多项式恒等式不能像 LP 那样重认证后恰好成立——桥接方式是
"舍入＋精确残差折减"（GAP-REPORT.md ③-6 的 (a)(b)(c)(d) 四缺步全链落地）：

  0) 数据源：确定性复跑 sdp_bound.solve_case(9, −0.9, 8, 6)（Round 1 审计确认
     逐位可复现），并与 sdp.json 存档值核对；解数据（h, e, F_k, 8 个 SOS Gram
     B_r, σ_0..σ_3）落盘 results/sdp_solution_midlarge_m090.json（Float、可
     --solution 复用，不再依赖求解器）。
  1) 舍入（安全方向 → 分母 2^k 的 dyadic 有理数，Fraction 精确）：
     h 最近舍入；e 向下（floor，只减不增）；F_k / B_r / σ_i 最近舍入后做
     **PSD 修复**——按浮点 λmin 亏损估计取最小充分 dyadic δ（≥2⁻⁴⁰ 地板），
     B ← B + δI（向上平移恢复 λmin ≥ 0），用 thomson_certs/exact.py 的
     无主元 LDLᵀ（纯 Fraction）验证严格正定，失败则 δ 翻倍重试。
     存进证书的就是修复后的块。
  2) 精确装配镜像：assemble_maps / SOS 块 / minorant 映射全部用 Fraction 重写
     （a = −9/10 精确，非 float −0.9），结构与浮点版逐项对齐（形状/索引全等、
     系数数值一致到 1e-6），并在随机有理点上做两个**精确**自检：
     (c) 三点恒等式 dsum(slack) + 7·Σ_all = 14·(ΣH − e) 逐位相等（==0 的
         Fraction 等式，随机有理 config × 随机 dyadic (h,e,F)，三次）；
     (b) 引理 4.1 正性 Σ_all ≥ 0 精确成立（随机有理 config × 随机 dyadic PSD F）。
  3) 精确残差与界值（全部 Fraction，无浮点）：
       resid_slack := slack_vec − SOS_vec（680 个单项式系数，slack_vec =
         Ch·h + c_e·e − R·F，SOS_vec = Σ_r map_r(B_r)），
       R1 := Σ_α |resid_slack,α|（域上 |u|,|v|,|t| ≤ 1 ⇒ 逐点 |resid| ≤ R1）；
       resid_σ := (Cp·h + p_const) − Σ_r map_r^σ(σ_r)（30 个 y 幂系数），
       R2 := |resid_σ,0| + (39/40)·Σ_{j≥1}|resid_σ,j|（y ∈ [0, b]，
         b = √(19/20) < 39/40 ⇒ 逐点 |resid_σ| ≤ R2）。
     界值公式（对一切 min_{i<j}⟨x_i,x_j⟩ ≥ −9/10 的 9 点构型，推导见下）：
       certified := (e − 36·R1) / (1 + R2)。
  4) 证书：certificates/n9-stage-a2-sdp.json（thomson_certs/schema.py 格式，
     blocks 存 e / h_diag / F0..F5 / B_1,B_u-a,…,B_detG / sig0..sig3 的全部
     'p/q' 字符串）；回读 decode + 再编码逐字节一致，并**从 JSON 块重建全部
     数据重算 certified** 与 claimed_bound 逐位比对（自含可复核）。

界值公式的推导（证书 provenance 里同步记录；结构性定理引用 N=7 论文
PAPER.md §4–5.1 / KLT arXiv:2609.22077，机器侧由上述精确自检＋构造自检覆盖）：

  记 H(t) = Σ_j h_j t^j（d_H=14），slack(u,v,t) := (H(u)+H(v)+H(t))/3 − e/36
  − R_s(u,v,t)，s = Σ_k⟨F_k, S_k⟩，R_s = 7·S + Σ_slot s(x,x,1) + s(1,1,1)/8。
  (i)  三点恒等式（对任意 (h,e,F) 的多项式恒等式，精确自检 (c)）：
       dsum(slack) + 7·Σ_all = 14·(ΣH − e)；
  (ii) Σ_all ≥ 0：F_k ⪰ 0（LDLᵀ 已验）＋引理 4.1（精确自检 (b) 实例验证）；
  (iii) slack ≥ −R1 于一切 Gram 三点：slack = SOS + resid_slack，SOS ≥ 0
       （B_r ⪰ 0，乘子 g_r ∈ {1, u+9/10, v+9/10, t+9/10, 1−u, 1−v, 1−t,
       detG} 在域 u,v,t ∈ [−9/10,1]、detG ≥ 0 上非负，z_r 分量 |·| ≤ 1），
       |resid_slack| ≤ R1（|u|,|v|,|t| ≤ 1）⇒ dsum(slack) ≥ −504·R1
       （dsum 取遍 9·8·7 = 504 个有序相异三点）；
       由 (i)–(iii)：ΣH ≥ e − 36·R1；
  (iv) minorant：1 − 2y·H(1−2y²) = σ_0 + yσ_1 + (b²−y²)σ_2 + y(b²−y²)σ_3
       + resid_σ ≥ −R2 于 y ∈ [0, b]（σ_i ⪰ 0 已验；b² = 19/20 精确），代入
       y = √((1−t)/2) 得 H(t) ≤ (1+R2)·φ(t)，φ = (2−2t)^(−1/2)，t ∈ [−9/10,1)；
       于是 E(x) = Σφ ≥ ΣH/(1+R2) ≥ (e − 36·R1)/(1+R2)。

断言（违反打印原因并 sys.exit(1)）：
  精确自检 (b)(c) 全过；全部 18 个 PSD 块经 exact.is_positive_definite；
  e − 36·R1 > 0；certified > 纪录线（--min-bound 覆盖；默认 LP 严格纪录
  certificates/n9-stage-a.json 的 claimed_bound ≈ 25.729490962）；certified ≤
  E* + 1e-6（E* 读 thomson-workflow/data/energies.json 的 9 位小数 value，精确
  十进制）；回读重算逐位一致。若某舍入粒度不过，自动换更细粒度重试（--k 列表）。

用法（认证路径不依赖 cvxpy——无 cvxpy 的解释器自动回退到已提交的解数据并明示；
求解路径需要 numerics/.venv）：
  python3 numerics/bounds/sdp_certify.py                                  # 认证（无 cvxpy 亦可）
  numerics/.venv/bin/python numerics/bounds/sdp_certify.py               # 求解+认证
  numerics/.venv/bin/python numerics/bounds/sdp_certify.py --solve-only  # 只求解落盘
  numerics/.venv/bin/python numerics/bounds/sdp_certify.py --solution \
      numerics/bounds/results/sdp_solution_midlarge_m090.json         # 指定解数据
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
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]                                    # .../thomson-n9
WORKFLOW_CERTS = HERE.parents[2] / "thomson-workflow" / "certificates"
sys.path.insert(0, str(HERE))                             # sdp_bound / lp_bound
sys.path.insert(0, str(WORKFLOW_CERTS))                   # thomson_certs

import sdp_bound                                          # noqa: E402
from thomson_certs.exact import is_positive_definite      # noqa: E402
from thomson_certs.schema import (                        # noqa: E402
    Certificate, decode_certificate, encode_certificate, fraction_to_str)

F0, F1 = Fraction(0), Fraction(1)

N, M, K = 9, 8, 6                                          # midlarge
A_EXACT = Fraction(-9, 10)                                 # 切口（精确有理数）
N2 = N * (N - 1) // 2                                      # 36
NTRIP = N * (N - 1) * (N - 2)                              # 504
D = 2 * M - 2                                              # 14
B_W = Fraction(39, 40)                                     # > b = √(19/20)，R2 权重
PHI_TOL = Fraction(1, 10 ** 6)


def fail(msg: str) -> None:
    print(f"[FAIL] {msg}", flush=True)
    sys.exit(1)


def code_version() -> str:
    """生成证书/结果时的代码版本（git describe --always --dirty）。

    防 M6 式复现尾差：复算员曾发现代码版本演进导致 −3.7e-9 级尾差，
    每份产物记录其生成代码的版本串。
    """
    try:
        return subprocess.check_output(
            ["git", "describe", "--always", "--dirty"], cwd=str(REPO),
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown(non-git)"


# ============================================================ 精确装配（Fraction 镜像）
class ExactMaps:
    """sdp_bound.assemble_maps ＋ SOS 块 ＋ minorant 映射的纯 Fraction 镜像。

    单项式索引/块结构复用 sdp_bound.Poly3 的整数逻辑（确定性、与浮点版全等），
    系数全部用 Fraction 重算（a = −9/10 精确）。
    """

    def __init__(self, n: int, a: Fraction, M: int, K: int):
        Dl = 2 * M - 2
        self.n, self.a, self.M, self.K = n, a, M, K
        self.D, self.d_H = Dl, Dl
        self.ring = sdp_bound.Poly3(Dl)                    # 结构：mons/index/perm_maps
        ring = self.ring
        self.nmon = ring.nmon
        self.F_sizes = [M - k for k in range(K)]
        # ---- Q_k（精确递推，同 build_Q）----
        def zero():
            return [F0] * self.nmon

        def mono(e, c):
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
                    e = (ep[0] + eq[0], ep[1] + eq[1], ep[2] + eq[2])
                    out[ring.index[e]] += ca * cb
            return out

        t_m_uv = [x - y for x, y in zip(mono((0, 0, 1), F1), mono((1, 1, 0), F1))]  # t−uv
        om = [x + y for x, y in zip(
            [x - y for x, y in zip(
                [x - y for x, y in zip(mono((0, 0, 0), F1), mono((2, 0, 0), F1))],
                mono((0, 2, 0), F1))], mono((2, 2, 0), F1))]          # (1−u²)(1−v²)
        Qs = [mono((0, 0, 0), F1), t_m_uv]
        while len(Qs) < K:
            prev1 = [2 * x for x in mul(t_m_uv, Qs[-1])]
            prev2 = mul(om, Qs[-2])
            Qs.append([x - y for x, y in zip(prev1, prev2)])
        self.Qs = Qs[:K]

        # ---- Ch、c_e ----
        n2 = n * (n - 1) // 2
        self.Ch = [[F0] * (self.d_H + 1) for _ in range(self.nmon)]   # Ch[mono][j]
        for j in range(self.d_H + 1):
            for slot in range(3):
                e = [0, 0, 0]
                e[slot] = j
                self.Ch[ring.index[tuple(e)]][j] += Fraction(1, 3)
        self.c_e = zero()
        self.c_e[ring.index[(0, 0, 0)]] = Fraction(-1, n2)

        # ---- S_cols / R_cols（同 assemble_maps 的循环序）----
        def symmetrize(v):
            out = [F0] * self.nmon
            for pm in ring.perm_maps:
                out = [x + v[pm[j]] for j, x in enumerate(out)]
            return [x / 6 for x in out]

        def subst_xx1(v, slot):
            out = zero()
            for p, c in enumerate(v):
                if c == 0:
                    continue
                i, j, _l = ring.mons[p]
                e = [0, 0, 0]
                e[slot] = i + j
                out[ring.index[tuple(e)]] += c
            return out

        self.S_cols, self.R_cols, self.S_index = [], [], {}
        for k in range(K):
            m_k = M - k
            for a_ in range(m_k):
                for b_ in range(m_k):
                    Y = [c for c in mul(mono((a_, b_, 0), F1), Qs[k])]
                    S = symmetrize(Y)
                    R = [(n - 2) * c for c in S]
                    for slot in range(3):
                        sub = subst_xx1(S, slot)
                        R = [x + y for x, y in zip(R, sub)]
                    R[ring.index[(0, 0, 0)]] += sum(S) / (n - 1)
                    self.S_index[(k, a_, b_)] = len(self.S_cols)
                    self.S_cols.append(S)
                    self.R_cols.append(R)

        # ---- SOS 块（同 build_sdp 的 blocks 构造；a 精确）----
        def unit(slot):
            e = [0, 0, 0]
            e[slot] = 1
            return tuple(e)

        def mons_upto(dmax):
            return [e for e in ring.mons if sum(e) <= dmax]

        detg = [((0, 0, 0), F1), ((1, 1, 1), Fraction(2)), ((2, 0, 0), Fraction(-1)),
                ((0, 2, 0), Fraction(-1)), ((0, 0, 2), Fraction(-1))]
        blocks = [("1", [((0, 0, 0), F1)], mons_upto(Dl // 2))]
        for var, slot in (("u", 0), ("v", 1), ("t", 2)):
            blocks.append((f"{var}-a", [((0, 0, 0), -a), (unit(slot), F1)],
                           mons_upto((Dl - 1) // 2)))
        for var, slot in (("u", 0), ("v", 1), ("t", 2)):
            blocks.append((f"1-{var}", [((0, 0, 0), F1), (unit(slot), Fraction(-1))],
                           mons_upto((Dl - 1) // 2)))
        blocks.append(("detG", detg, mons_upto((Dl - 3) // 2)))
        self.sos_blocks = blocks                            # [(name, g_nonzeros, mons)]

        # ---- minorant 映射（同 build_sdp 的 Csub/Cp/sig_def；b2 精确）----
        self.b2 = (F1 - a) / 2
        self.deg_p = 2 * self.d_H + 1
        self.Csub = [[F0] * (self.d_H + 1) for _ in range(self.deg_p + 1)]
        for i in range(self.d_H + 1):
            for m in range(i + 1):
                self.Csub[2 * m][i] += Fraction(math.comb(i, m) * ((-2) ** m))
        self.Cp = [[F0] * (self.d_H + 1) for _ in range(self.deg_p + 1)]
        for r in range(1, self.deg_p + 1, 2):
            self.Cp[r] = [-2 * x for x in self.Csub[r - 1]]
        self.p_const = [F0] * (self.deg_p + 1)
        self.p_const[0] = F1
        self.sig_def = [("sig0", list(range(0, self.d_H + 1)), [(0, F1)]),
                        ("sig1", list(range(0, self.d_H + 1)), [(1, F1)]),
                        ("sig2", list(range(0, self.d_H)), [(0, self.b2), (2, Fraction(-1))]),
                        ("sig3", list(range(0, self.d_H)),
                         [(1, self.b2), (3, Fraction(-1))])]

    # ---------------- 求值（精确）----------------
    def eval3(self, vec, u: Fraction, v: Fraction, t: Fraction) -> Fraction:
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


def sos_vec(em: ExactMaps, Bblocks: dict[str, list[list[Fraction]]]) -> list[Fraction]:
    """Σ_r map_r(vec(B_r))：g_r·z_rᵀB_r z_r 的单项式系数向量（精确）。"""
    out = [F0] * em.nmon
    ring = em.ring
    for name, gnz, mons in em.sos_blocks:
        B = Bblocks[name]
        m = len(mons)
        for p in range(m):
            ep = mons[p]
            row = B[p]
            for q in range(m):
                c = row[q]
                if c == 0:
                    continue
                eq = mons[q]
                base = (ep[0] + eq[0], ep[1] + eq[1], ep[2] + eq[2])
                for (eg, cg) in gnz:
                    e = (base[0] + eg[0], base[1] + eg[1], base[2] + eg[2])
                    out[ring.index[e]] += c * cg
    return out


def slack_vec(em: ExactMaps, h: list[Fraction], e: Fraction,
              Fblocks: list[list[list[Fraction]]]) -> list[Fraction]:
    """Ch·h + c_e·e − R·vec(F)（精确；列序同 S_index 的 (k,a_,b_) 行主序）。"""
    out = [F0] * em.nmon
    for i in range(em.nmon):
        acc = sum(em.Ch[i][j] * h[j] for j in range(em.d_H + 1))
        out[i] = acc
    out[em.ring.index[(0, 0, 0)]] += em.c_e[em.ring.index[(0, 0, 0)]] * e
    for k, m_k in enumerate(em.F_sizes):
        Fk = Fblocks[k]
        for a_ in range(m_k):
            for b_ in range(m_k):
                c = Fk[a_][b_]
                if c == 0:
                    continue
                R = em.R_cols[em.S_index[(k, a_, b_)]]
                for p, rc in enumerate(R):
                    if rc:
                        out[p] -= c * rc
    return out


def minorant_lhs(em: ExactMaps, sig_blocks: dict[str, list[list[Fraction]]]
                 ) -> list[Fraction]:
    """Σ_r map_r^σ(vec(σ_r))（精确；行 = y 的次数 0..deg_p）。"""
    out = [F0] * (em.deg_p + 1)
    for name, mons_y, mult in em.sig_def:
        S = sig_blocks[name]
        m = len(mons_y)
        for p in range(m):
            row = S[p]
            for q in range(m):
                c = row[q]
                if c == 0:
                    continue
                base = mons_y[p] + mons_y[q]
                for (eg, cg) in mult:
                    out[base + eg] += c * cg
    return out


def minorant_rhs(em: ExactMaps, h: list[Fraction]) -> list[Fraction]:
    out = [F0] * (em.deg_p + 1)
    for r in range(em.deg_p + 1):
        out[r] = sum(em.Cp[r][j] * h[j] for j in range(em.d_H + 1)) + em.p_const[r]
    return out


# ============================================================ dyadic 舍入与 PSD 修复
def dyad(x, k: int, floor: bool = False) -> Fraction:
    """float/Fraction → 最近（或向下）的 2^-k 网格 Fraction。

    float 输入：x·2^k 是精确浮点运算，但要求 |x|·2^k < 2^53（超出则格点
    定位带浮点噪声）。Fraction 输入（高精度解的 exact 字段）：纯整数运算，
    任意数量级都精确——σ 块尺度 ~1e10 时 float64 尾数只剩 ~19 位，必须走
    这条路。"""
    if isinstance(x, Fraction):
        n = x * (1 << k)                          # 精确 Fraction
        p = n.numerator // n.denominator          # floor
        if not floor:
            # 最近舍入（半向上；n 非负/负均一致处理）
            p = (2 * n.numerator + n.denominator) // (2 * n.denominator)
        return Fraction(p, 1 << k)
    q = float(1 << k)
    v = x * q
    p = math.floor(v) if floor else int(round(v))
    return Fraction(p, 1 << k)


def next_dyadic_above(x: float) -> Fraction:
    """最小的 2 的幂（2^-j）≥ x，x > 0。"""
    j = 0
    while 2.0 ** -(j + 1) >= x:
        j += 1
    return Fraction(1, 2 ** j)


def repair_psd(name: str, Mfr: list[list[Fraction]], k: int):
    """PSD 修复：M ← M + δI（δ 为最小充分 dyadic，2^-40 地板起）。

    浮点解的块略不定（λmin ~ −1e-7），向上平移对角元恢复半正定：
    λmin(M+δI) = λmin(M) + δ。δ 一律从 2^-40 地板起步、exact LDLᵀ 验证
    严格正定、失败翻倍（≤45 次，可爬到 >1）——最小充分 δ 由**精确**判定
    决定，而不是 float64 eigvalsh 亏损估计：大尺度块（σ ~1e10）的估计噪声
    ~1e-16·‖M‖ ≈ 1e-6，按估计起步会把噪声余量固化进 δ 而无谓吃掉认证精度。
    返回 (修复后矩阵, δ, 尝试次数)。
    """
    n = len(Mfr)
    delta = Fraction(1, 1 << 40)
    for attempt in range(1, 46):
        out = [[Mfr[i][j] + (delta if i == j else F0) for j in range(n)]
               for i in range(n)]
        if is_positive_definite(out):
            return out, delta, attempt
        delta = delta * 2
    fail(f"块 {name} 的 PSD 修复 45 次尝试后仍失败")


# ============================================================ 精确自检
def rational_point(a: Fraction, b: Fraction):
    s = 1 + a * a + b * b
    return (2 * a / s, 2 * b / s, (1 - a * a - b * b) / s)


def random_dyadic_config(rng, n, bits=8):
    return [rational_point(Fraction(rng.randint(-1 << bits, 1 << bits), 1 << bits),
                           Fraction(rng.randint(-1 << bits, 1 << bits), 1 << bits))
            for _ in range(n)]


def exact_identity_selftest(em: ExactMaps, rng, trials=3):
    """(c) 三点恒等式：随机有理 config × 随机 dyadic (h, e, PSD F) 上精确 == 0。"""
    worst = None
    for _ in range(trials):
        h = [Fraction(rng.randint(-1 << 16, 1 << 16), 1 << 16) for _ in range(em.d_H + 1)]
        e = Fraction(rng.randint(-1 << 16, 1 << 16), 1 << 16)
        Fblocks = []
        for m_k in em.F_sizes:
            G = [[Fraction(rng.randint(-8, 8), 4) for _ in range(m_k)] for _ in range(m_k)]
            Fk = [[sum(G[i][t] * G[j][t] for t in range(m_k)) for j in range(m_k)]
                  for i in range(m_k)]
            Fblocks.append(Fk)
        X = random_dyadic_config(rng, em.n)
        G = [[sum(xi[k] * xj[k] for k in range(3)) for xj in X] for xi in X]
        n = em.n
        s_vec = [F0] * em.nmon
        slack = slack_vec(em, h, e, Fblocks)
        for k, m_k in enumerate(em.F_sizes):
            for a_ in range(m_k):
                for b_ in range(m_k):
                    c = Fblocks[k][a_][b_]
                    if c:
                        s_vec = [x + c * y for x, y in
                                 zip(s_vec, em.S_cols[em.S_index[(k, a_, b_)]])]
        dsum = F0
        sall = F0
        for i in range(n):
            for j in range(n):
                for l in range(n):
                    val = em.eval3(s_vec, G[i][j], G[i][l], G[j][l])
                    sall += val
                    if i != j and j != l and i != l:
                        dsum += em.eval3(slack, G[i][j], G[i][l], G[j][l])
        sumH = F0
        for i in range(n):
            for j in range(i + 1, n):
                t = G[i][j]
                acc = F0
                tp = F1
                for jj in range(em.d_H + 1):
                    acc += h[jj] * tp
                    tp *= t
                sumH += acc
        lhs = dsum + (n - 2) * sall
        rhs = 2 * (n - 2) * (sumH - e)
        if lhs != rhs:
            fail(f"精确三点恒等式自检失败：lhs−rhs = {lhs - rhs}（非零 Fraction）")
        worst = float(lhs - rhs) if worst is None else worst
    return dict(trials=trials, exact_zero=True, note="dsum+7Σ_all == 14(ΣH−e) 精确成立")


def exact_positivity_selftest(em: ExactMaps, rng, trials=3):
    """(b) 引理 4.1：随机有理 config × 随机 dyadic PSD F ⇒ Σ_all ≥ 0 精确。

    先把 Σ_k⟨F_k,S_k⟩ 聚成系数向量 s_vec，再在全部 n³ 有序三点上精确求值。
    """
    mins = []
    for _ in range(trials):
        X = random_dyadic_config(rng, em.n)
        G = [[sum(xi[k] * xj[k] for k in range(3)) for xj in X] for xi in X]
        s_vec = [F0] * em.nmon
        for k, m_k in enumerate(em.F_sizes):
            Gm = [[Fraction(rng.randint(-8, 8), 4) for _ in range(m_k)] for _ in range(m_k)]
            Fk = [[sum(Gm[i][t] * Gm[j][t] for t in range(m_k)) for j in range(m_k)]
                  for i in range(m_k)]
            for a_ in range(m_k):
                for b_ in range(m_k):
                    c = Fk[a_][b_]
                    if c:
                        col = em.S_cols[em.S_index[(k, a_, b_)]]
                        s_vec = [x + c * y for x, y in zip(s_vec, col)]
        sall = sum(em.eval3(s_vec, G[i][j], G[i][l], G[j][l])
                   for i in range(em.n) for j in range(em.n) for l in range(em.n))
        if sall < 0:
            fail(f"精确正性自检失败：Σ_all = {sall} < 0")
        mins.append(float(sall))
    return dict(trials=trials, all_nonneg=True, min_float=min(mins))


def cross_check_float_maps(em: ExactMaps, maps_float):
    """结构逐项全等（形状/索引），系数数值一致到 1e-6（a=−9/10 vs float −0.9）。"""
    assert em.nmon == maps_float["ring"].nmon
    assert em.ring.mons == maps_float["ring"].mons
    assert em.ring.index == maps_float["ring"].index
    assert em.F_sizes == maps_float["F_sizes"]
    # SOS 块结构与 minorant 映射对齐（单项式表与整数结构全等；系数一致到 1e-6，
    # 差异仅来自 a=−9/10 精确 vs float −0.9 与 1/3 等的浮点舍入）
    ring = sdp_bound.Poly3(em.D)
    mons_upto = lambda dmax: [e for e in ring.mons if sum(e) <= dmax]
    expect_sizes = [len(mons_upto(em.D // 2))] + \
        [len(mons_upto((em.D - 1) // 2))] * 6 + [len(mons_upto((em.D - 3) // 2))]
    got_sizes = [len(m) for _name, _g, m in em.sos_blocks]
    assert got_sizes == expect_sizes, f"SOS 块尺寸不一致: {got_sizes} vs {expect_sizes}"
    diffs = []
    for i in range(len(em.S_cols)):
        a = np.array([float(x) for x in em.S_cols[i]])
        b = maps_float["S_cols"][i]
        diffs.append(float(np.max(np.abs(a - b))))
    for i in range(len(em.R_cols)):
        a = np.array([float(x) for x in em.R_cols[i]])
        b = maps_float["R_cols"][i]
        diffs.append(float(np.max(np.abs(a - b))))
    worst = max(diffs)
    if worst > 1e-6:
        fail(f"精确装配与浮点装配的 S/R 列最大偏差 {worst:.3e} > 1e-6")
    # Ch / c_e
    chf = np.array([[float(em.Ch[i][j]) for j in range(em.d_H + 1)]
                    for i in range(em.nmon)])
    if float(np.max(np.abs(chf - maps_float["Ch"]))) > 1e-9:
        fail("Ch 与浮点版不一致")
    return worst


# ============================================================ 主流程
def main() -> None:
    ap = argparse.ArgumentParser(description="三点 SDP 下界（midlarge m=−0.90）精确证书")
    ap.add_argument("--k", type=int, nargs="+", default=[48, 56, 64],
                    help="dyadic 舍入粒度候选（分母 2^-k），依次尝试直到断言全过")
    ap.add_argument("--k-sig", type=int, default=None,
                    help="σ 块独立 dyadic 粒度（默认按最大条目自动：max|σ|·2^k < 2^52；"
                         "σ 尺度 ~1e3 以上时 2^-48 网格在 float64 里放不下）")
    ap.add_argument("--min-bound", type=float, default=None,
                    help="certified 必须严格超过的纪录线（默认 LP 证书 "
                         "certificates/n9-stage-a.json 的 claimed_bound ≈ 25.729490962；"
                         "高精度解认证传 Round 2 的 25.752410818）")
    ap.add_argument("--ref-safe", type=float, default=None,
                    help="覆盖 rounding_loss 参考的数值折减界 e_safe（默认读 "
                         "results/sdp.json 的 Round 1 存档值；--solution 换解数据时"
                         "应传该解自己的 e_safe）")
    ap.add_argument("--solution", type=str, default=None,
                    help="复用已落盘的解数据 JSON（跳过求解）")
    ap.add_argument("--solve-only", action="store_true",
                    help="只求解并落盘解数据，不做认证")
    ap.add_argument("--out", type=str,
                    default=str(REPO / "certificates" / "n9-stage-a2-sdp.json"))
    args = ap.parse_args()

    t_start = time.time()
    sol_path = HERE / "results" / "sdp_solution_midlarge_m090.json"

    # ---- 参考值 ----
    with open(HERE.parents[2] / "thomson-workflow" / "data" / "energies.json") as f:
        # Fraction(str(...))＝十进字面值精确化。json 数值反序列化得到 float，
        # 直接 Fraction(float) 会得到 float64 的二进精确值（7250791608880037/2^48，
        # 与十进口径 25759986531/10^9 差 8.67e-16）——R4 期存档 HP 证书
        # provenance.gap_to_E_star.exact 即旧口径，R7 复核勘误见 decisions D17；
        # 本证书与 endgame_chain.py frac()/endgame_gate.py 统一十进口径。
        E_star = Fraction(str(json.load(f)["energies"]["9"]["value"]))
    lp_cert = json.loads((REPO / "certificates" / "n9-stage-a.json").read_text())
    LP_RECORD = Fraction(lp_cert["claimed_bound"])
    RECORD = Fraction(str(args.min_bound)) if args.min_bound is not None else LP_RECORD
    with open(HERE / "results" / "sdp.json") as f:
        sdpj = json.load(f)
    case = next(c for c in sdpj["cases"]
                if c["m"] == -0.9 and c["config"] == "midlarge")
    e_stored, e_safe_stored = case["e"], case["check"]["e_safe"]
    ref_desc = "results/sdp.json Round 1 存档"
    print(f"[load] E* = {float(E_star):.9f}；LP 纪录 = {float(LP_RECORD):.12f}；"
          f"纪录线 = {float(RECORD):.12f}；"
          f"sdp.json midlarge: e = {e_stored!r}, e_safe = {e_safe_stored!r}", flush=True)

    # ---- 0) 数据源：确定性复跑或读盘 ----
    # 求解路径需要 cvxpy（numerics/.venv 解释器）；认证路径不需要——当前解释器
    # 无 cvxpy 时显式回退到已落盘并提交的解数据（打印明示、provenance 记录），
    # 绝不静默。
    if args.solution:
        with open(args.solution) as f:
            sol = json.load(f)
        src_desc = f"复用解数据 {args.solution}"
    elif sdp_bound.cp is None:
        if not sol_path.exists():
            fail("当前解释器无 cvxpy 且无已落盘解数据：请用 "
                 "numerics/.venv/bin/python 运行（求解），或先在有 cvxpy 的环境"
                 f"生成 {sol_path}（--solve-only）")
        with open(sol_path) as f:
            sol = json.load(f)
        src_desc = (f"当前解释器无 cvxpy，显式回退到已提交的解数据 "
                    f"{sol_path.relative_to(REPO)}（其生成运行经 venv 复跑与 "
                    "results/sdp.json 存档逐位一致，见该文件 rerun_e_matches_stored）")
        print(f"[solve] cvxpy 不可用——回退到已落盘解数据 {sol_path}"
              f"（存在、sha 见 provenance），不重新求解", flush=True)
    else:
        print("[solve] sdp_bound.solve_case(9, -0.9, M=8, K=6)（Clarabel，~4 分钟）…",
              flush=True)
        t0 = time.time()
        e_val, info, chk, maps_float, V = sdp_bound.solve_case(9, -0.9, M, K)
        print(f"[solve] e = {e_val!r}（{info['solver']} {info['status']}，"
              f"{time.time() - t0:.0f}s）", flush=True)
        if info["status"] not in ("optimal", "optimal_inaccurate"):
            fail(f"复跑求解状态异常：{info['status']}")
        if e_val != e_stored:
            print(f"[warn] 复跑 e = {e_val!r} 与存档 {e_stored!r} 不逐位一致"
                  f"（差 {e_val - e_stored:.3e}），以复跑值为证书数据源并记录", flush=True)
        else:
            print("[solve] 复跑 e 与 sdp.json 存档逐位一致 ✓", flush=True)
        sol = dict(
            h=[float(x) for x in V["h"].value],
            e=float(V["e"].value),
            F=[((np.asarray(Fk.value) + np.asarray(Fk.value).T) / 2).tolist()
               for Fk in V["F"]],
            B={name: ((np.asarray(Bv.value) + np.asarray(Bv.value).T) / 2).tolist()
               for name, _A, Bv in V["sos"]},
            sig={name: ((np.asarray(Bv.value) + np.asarray(Bv.value).T) / 2).tolist()
                 for name, _A, Bv, _my, _mu in V["sig"]},
            solver_info={k2: v for k2, v in info.items()},
            verify=chk,
            rerun_e_matches_stored=bool(e_val == e_stored),
            timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        )
        sol_path.parent.mkdir(parents=True, exist_ok=True)
        txt = json.dumps(sol, ensure_ascii=False)
        sol_path.write_text(txt)
        print(f"[out] 解数据已落盘 {sol_path}（{len(txt)} 字节）", flush=True)
        src_desc = ("确定性复跑 solve_case(9,−0.9,8,6)，解数据存 "
                    f"{sol_path.relative_to(REPO)}")
    if args.solve_only:
        print("[done] --solve-only 完成", flush=True)
        return

    # --ref-safe：解数据不是 sdp.json 存档的那份时，rounding_loss 的参考值换成
    # 该解自己的数值折减界（诚实标注参考来源），避免拿旧 e_safe 冒充新解的损失
    if args.ref_safe is not None:
        e_stored, e_safe_stored = float(sol["e"]), float(args.ref_safe)
        ref_desc = f"--ref-safe 覆盖（e_safe = {args.ref_safe!r}）"
        print(f"[ref  ] rounding_loss 参考已覆盖：e_stored = {e_stored!r}, "
              f"e_safe_ref = {e_safe_stored!r}", flush=True)

    # 解数据：优先 exact 字段（精确 p/q 有理数——SDPA-GMP 高精度解 66 位十进制
    # 的精确回读；dyadic 舍入走整数运算，σ 块 ~1e10 尺度不丢格点），否则 float
    # 字段（Round 1 Clarabel 解数据，兼容旧路径）。
    if "exact" in sol:
        ex = sol["exact"]
        h_fl = [Fraction(s) for s in ex["h"]]
        e_fl = Fraction(ex["e"])
        F_fl = [[[Fraction(s) for s in row] for row in m_] for m_ in ex["F"]]
        B_fl = {n: [[Fraction(s) for s in row] for row in m_]
                for n, m_ in ex["B"].items()}
        sig_fl = {n: [[Fraction(s) for s in row] for row in m_]
                  for n, m_ in ex["sig"].items()}
        print("[load] 使用 exact 字段（精确有理数）做 dyadic 舍入 ✓", flush=True)
    else:
        h_fl = sol["h"]
        e_fl = sol["e"]
        F_fl = sol["F"]
        B_fl = sol["B"]
        sig_fl = sol["sig"]
    sol_sha = hashlib.sha256(json.dumps(
        {k2: sol[k2] for k2 in ("h", "e", "F", "B", "sig")},
        sort_keys=True).encode()).hexdigest()[:16]

    # ---- 1) 精确装配镜像 + 结构交叉核对 + 精确自检 ----
    em = ExactMaps(N, A_EXACT, M, K)
    maps_float = sdp_bound.assemble_maps(N, -0.9, M, K)
    xdiff = cross_check_float_maps(em, maps_float)
    print(f"[maps] 精确镜像 vs 浮点装配：结构全等，S/R 列最大系数偏差 "
          f"{xdiff:.2e}（a=−9/10 vs float −0.9）✓", flush=True)
    rng = random.Random(20261003)
    id_chk = exact_identity_selftest(em, rng)
    pos_chk = exact_positivity_selftest(em, rng)
    print(f"[selftest] 精确三点恒等式 {id_chk['trials']} 次全为 ==0 ✓；"
          f"精确正性 {pos_chk['trials']} 次全 ≥0 ✓", flush=True)

    # ---- 2)+3) 舍入 → PSD 修复 → 精确残差 → 界值（按粒度依次尝试）----
    # σ 块粒度：默认与其余块相同（exact 字段的 Fraction 舍入走整数运算，任意
    # 数量级都精确）；--k-sig 仅作显式覆盖（旧 float 解数据路径才可能需要）。
    sig_max = max(max(abs(float(x)) for row in sig_fl[name] for x in row)
                  for name, _my, _mu in em.sig_def) if sig_fl else 0.0
    k_sig = args.k_sig if args.k_sig is not None else (args.k[0] if args.k else 48)
    if not all(isinstance(x, Fraction) for row in sig_fl[em.sig_def[0][0]] for x in row):
        if sig_max * 2.0 ** k_sig >= 2.0 ** 52:
            print(f"[warn ] σ 块最大条目 {sig_max:.3e} × 2^{k_sig} ≥ 2^52 且解为"
                  f"float 数据：dyadic 网格定位将带 float64 噪声（考虑 --k-sig）",
                  flush=True)
    print(f"[round] σ 块粒度 2^-{k_sig}（最大条目 {sig_max:.3e}）；其余 2^-k", flush=True)
    last_err = None
    for k in args.k:
        try:
            result = certify_at(em, k, h_fl, e_fl, F_fl, B_fl, sig_fl,
                                E_star, RECORD, e_stored, e_safe_stored,
                                k_sig=k_sig)  # RECORD 别名转发，签名保持 LP_RECORD 兼容 cap_ladder
        except SystemExit as exc:            # fail() 触发：换更细粒度重试
            last_err = exc.code
            print(f"[retry] 粒度 2^-{k} 未通过断言，换更细粒度重试", flush=True)
            continue
        break
    else:
        fail(f"全部粒度 {args.k} 均未通过断言（最后失败码 {last_err}）")

    (h_dy, e_dy, F_dy, B_dy, sig_dy, shifts, R1, R2, resid_l1_sig,
     certified, spot) = result
    loss_vs_esafe = float(Fraction(str(e_safe_stored)) - certified)
    print(f"[bound] certified = (e − 36·R1)/(1 + R2) = {float(certified):.12f}"
          f"（粒度 2^-{k}）", flush=True)
    print(f"[bound] R1 = {float(R1):.6e}（36·R1 = {float(36 * R1):.6e}），"
          f"R2 = {float(R2):.6e}（e·R2/(1+R2) = "
          f"{float(e_dy * R2 / (1 + R2)):.6e}）", flush=True)
    print(f"[loss ] 舍入损失 e_safe − certified = {loss_vs_esafe:.6e}"
          f"（e_raw − certified = {float(e_dy - certified):.6e}）", flush=True)

    # ---- 4) 证书 JSON ----
    blocks = {"e": [[fraction_to_str(e_dy)]]}
    blocks["h_diag"] = [[fraction_to_str(h_dy[j]) if i == j else "0"
                         for j in range(em.d_H + 1)] for i in range(em.d_H + 1)]
    for kk, m_k in enumerate(em.F_sizes):
        blocks[f"F{kk}"] = [[fraction_to_str(x) for x in row] for row in F_dy[kk]]
    for name, _gnz, _mons in em.sos_blocks:
        blocks[f"B_{name}"] = [[fraction_to_str(x) for x in row] for row in B_dy[name]]
    for name, _my, _mu in em.sig_def:
        blocks[name] = [[fraction_to_str(x) for x in row] for row in sig_dy[name]]

    prov = {
        "repo": "thomson-n9",
        "generator": ("numerics/bounds/sdp_certify.py（候选解来自 "
                      "numerics/bounds/sdp_bound.py 的 midlarge=(8,6) × m=−0.90 主界"
                      f"配置；{src_desc}）"),
        "date": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "upstream": ("thomson-workflow/certificates/thomson_certs（exact.py 无主元 "
                     "LDLᵀ ＋ schema.py 交接格式）；三点 SDP 构造自 N=7 证明 "
                     "references/thomson-n7-lean/paper/PAPER.md §4–5.1 移植"
                     "（KLT arXiv:2609.22077 §4.2–4.3 同框架）"),
        "params": {
            "N": N, "a": fraction_to_str(A_EXACT), "M": M, "K": K,
            "D": D, "d_H": D, "nmon": em.nmon, "F_sizes": em.F_sizes,
            "round_bits": k,
            "round_bits_sig": k_sig,
            "round_bits_sig_note": ("σ 块独立粒度（高精度解的 σ 尺度大时 2^-k "
                                    "网格在 float64 尾数里放不下，需更粗）；"
                                    "其余块/h/e 用 round_bits"),
            "b2_exact": fraction_to_str(em.b2),
            "R2_weight": "39/40（> b = sqrt(19/20) ≈ 0.9746794）",
            "scope": ("对一切 min_(i<j) ⟨x_i,x_j⟩ ≥ −9/10 的 9 点单位球面构型 "
                      "E(x) ≥ claimed_bound。**不**覆盖含更近对径对的构型——"
                      "[−1, −9/10) 的 slab 带未开始（GAP-REPORT.md ②③）"),
            "m_meaning": ("m_lo/m_hi 为本证书覆盖的最小内积胞腔 [−9/10, 1]；"
                          "u,v,t 的证书域即 [−9/10,1]³ ∩ {detG ≥ 0}"),
            "blocks_map": ("e[0][0]＝e；h_diag 对角线＝h_0..h_14（H(t)=Σh_j t^j）；"
                           "F0..F5＝F_k（尺寸 8..3）；B_1,B_u-a,B_v-a,B_t-a,"
                           "B_1-u,B_1-v,B_1-t,B_detG＝SOS 块 Gram 阵（乘子 g_r 与"
                           "单项式表 z_r 由 sdp_bound.build_sdp 的确定性构造重建，"
                           "M=8,K=6,D=14）；sig0..sig3＝minorant 的 Lukács 块"),
            "bound_formula": (
                "certified = (e − 36·R1)/(1 + R2)，其中 "
                "R1 = Σ_α |resid_slack_α|，resid_slack = slack_vec − SOS_vec 于"
                "680 个单项式系数（slack_vec = Ch·h + c_e·e − R·vec(F)，"
                "SOS_vec = Σ_r map_r(vec(B_r))，装配见 sdp_bound.assemble_maps / "
                "build_sdp / 本脚本 ExactMaps）；R2 = |resid_σ,0| + (39/40)·"
                "Σ_{j≥1}|resid_σ,j|，resid_σ = (Cp·h + p_const) − Σ_r map_r^σ"
                "(vec(σ_r))（30 个 y 幂系数）。推导：三点恒等式 dsum(slack) + "
                "7·Σ_all = 14·(ΣH − e)；Σ_all ≥ 0（F_k ⪰ 0 ＋引理 4.1）；"
                "slack ≥ −R1 于 Gram 域（SOS ≥ 0 ＋ |resid| ≤ R1，|u|,|v|,|t|≤1）；"
                "⇒ ΣH ≥ e − 36·R1（dsum 计 504 个有序相异三点）；"
                "1 − 2yH(1−2y²) ≥ −R2 于 y∈[0,b]（σ_i ⪰ 0）⇒ H ≤ (1+R2)·φ 于 "
                "[−9/10,1) ⇒ E = Σφ ≥ ΣH/(1+R2) ≥ (e − 36·R1)/(1+R2)"),
        },
        "numerical_bound": {
            "sdp_raw_e_rerun": float(e_fl), "sdp_raw_e_stored": e_stored,
            "e_safe_stored": e_safe_stored,
            "solver": sol.get("solver_info", {}),
            "solution_dump": str(sol_path.relative_to(REPO)),
            "solution_sha256_16": sol_sha,
        },
        "exact_bound": fraction_to_str(certified),
        "residual_norms": {
            "R1_exact": fraction_to_str(R1), "R1_float": float(R1),
            "R2_exact": fraction_to_str(R2), "R2_float": float(R2),
            "deflation_slack_36R1": float(36 * R1),
            "deflation_minorant": float(e_dy * R2 / (1 + R2)),
            "note": ("R1/R2 为舍入＋PSD 修复后数据的**精确**残差范数（纯 "
                     "Fraction 计算），含求解器恒等式残差与 δ 平移的全部贡献"),
        },
        "psd_shifts": {name: fraction_to_str(d) for name, d in shifts.items()},
        "rounding_loss": {
            "definition": f"数值折减界 e_safe − 精确界 certified（参考：{ref_desc}）",
            "float": loss_vs_esafe,
            "vs_raw_e_float": float(e_dy - certified),
            "components": {"36*R1": float(36 * R1),
                           "e*R2/(1+R2)": float(e_dy * R2 / (1 + R2))},
        },
        "checks": {
            "exact_maps_cross_check_float": True,
            "exact_three_point_identity_random_rational": id_chk,
            "exact_lemma4_1_positivity_random_rational": pos_chk,
            "all_blocks_exact_ldlt_positive_definite": True,
            "e_minus_36R1_positive": True,
            "sos_spot_nonneg_random_rational_gram_triples": spot["sos"],
            "resid_eval_consistency": spot["resid"],
            "minorant_squared_spot_checks": spot["minorant"],
            "certified_gt_record": fraction_to_str(LP_RECORD),
            "certified_le_Estar_plus_1e-6": True,
            "readback_recompute_bitwise": True,
        },
        "gap_to_E_star": {"exact": fraction_to_str(E_star - certified),
                          "float": float(E_star - certified)},
        "runtime_s": round(time.time() - t_start, 1),
        "code_version": code_version(),
        "repro": (
            "numerics/.venv/bin/python numerics/bounds/sdp_certify.py"
            + ((" " + " ".join(sys.argv[1:])) if sys.argv[1:] else "")
            + "（本证书的实际生成命令与粒度）。注意：不显式传 --k 时默认 "
              "[48, 56, 64] 取**首个通过断言**的粒度，粒度不同 certified 尾数不同"
              "（hp 解实测 k=48 比 k=64 低 3.58e-07，两值均有效）——逐位复现存档值"
              "须按上方命令的显式 --k"),
    }
    cert_obj = Certificate(m_lo=fraction_to_str(A_EXACT), m_hi="1",
                           blocks=blocks, claimed_bound=fraction_to_str(certified),
                           provenance=prov)
    text = encode_certificate(cert_obj)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(text)
    print(f"[out] 已写入 {out_path}（{len(text)} 字节）", flush=True)

    # 回读：decode → 从块重建数据 → 精确重算 certified → 逐位比对 → 再编码一致
    rt = decode_certificate(out_path.read_text())
    h2 = [Fraction(rt.blocks["h_diag"][j][j]) for j in range(em.d_H + 1)]
    e2 = Fraction(rt.blocks["e"][0][0])
    F2 = [[[Fraction(x) for x in row] for row in rt.blocks[f"F{kk}"]]
          for kk in range(len(em.F_sizes))]
    B2 = {name[2:]: [[Fraction(x) for x in row] for row in rt.blocks[name]]
          for name in [f"B_{gn}" for gn, _g, _m in em.sos_blocks]}
    sig2 = {name: [[Fraction(x) for x in row] for row in rt.blocks[name]]
            for name, _my, _mu in em.sig_def}
    cert2 = recompute_certified(em, h2, e2, F2, B2, sig2)
    if cert2 != certified:
        fail(f"回读重算不一致：{cert2} ≠ {certified}")
    if encode_certificate(rt) != text:
        fail("回读再编码与原文不逐字节一致")
    print("[rt  ] 回读重建 + 精确重算 certified 逐位一致 ✓ 再编码逐字节一致 ✓",
          flush=True)
    print(f"[done] certified bound = {float(certified):.12f}（> 纪录线 "
          f"{float(RECORD):.12f}，≤ E*+1e-6 ✓），舍入损失 = {loss_vs_esafe:.6e}，"
          f"总用时 {prov['runtime_s']}s", flush=True)


def recompute_certified(em, h, e, Fblocks, Bblocks, sigblocks):
    """从证书数据重算 certified（纯 Fraction；验证器可独立实现同一公式）。"""
    sv = slack_vec(em, h, e, Fblocks)
    ov = sos_vec(em, Bblocks)
    resid = [x - y for x, y in zip(sv, ov)]
    R1 = sum(abs(x) for x in resid)
    lhs = minorant_lhs(em, sigblocks)
    rhs = minorant_rhs(em, h)
    rsig = [x - y for x, y in zip(rhs, lhs)]
    R2 = abs(rsig[0]) + B_W * sum(abs(x) for x in rsig[1:])
    return (e - 36 * R1) / (1 + R2)


def certify_at(em, k, h_fl, e_fl, F_fl, B_fl, sig_fl,
               E_star, LP_RECORD, e_stored, e_safe_stored, k_sig=None):
    """一个舍入粒度上的完整认证链；任一断言失败 fail()（SystemExit）。

    k_sig：σ 块的独立 dyadic 粒度（默认 = k）。高精度解的 σ 块可能尺度
    ~1e3-1e4，float64 尾数只剩 ~40 位，2^-k 网格放不下（x·2^k 超 2^53 会
    带来格点错位），需按最大条目自动降粒度；h/e/F/B 仍用 k。
    """
    t0 = time.time()
    if k_sig is None or k_sig > k:
        k_sig = k
    # ---- 舍入 ----
    h_dy = [dyad(x, k) for x in h_fl]
    e_dy = dyad(e_fl, k, floor=True)
    F_dy, shifts = [], {}
    for kk, m_k in enumerate(em.F_sizes):
        Mfr = [[dyad(x, k) for x in row] for row in F_fl[kk]]
        Mfr, d, tries = repair_psd(f"F{kk}", Mfr, k)
        shifts[f"F{kk}"] = d
        F_dy.append(Mfr)
        print(f"[psd  ] F{kk}（{m_k}×{m_k}）：δ = {float(d):.3e}，LDLᵀ 正定 ✓"
              f"（{tries} 次）", flush=True)
    B_dy = {}
    for name, _gnz, _mons in em.sos_blocks:
        Mfr = [[dyad(x, k) for x in row] for row in B_fl[name]]
        Mfr, d, tries = repair_psd(f"B_{name}", Mfr, k)
        shifts[f"B_{name}"] = d
        B_dy[name] = Mfr
        print(f"[psd  ] B_{name}（{len(Mfr)}×{len(Mfr)}）：δ = {float(d):.3e}，"
              f"LDLᵀ 正定 ✓（{tries} 次）", flush=True)
    sig_dy = {}
    for name, _my, _mu in em.sig_def:
        Mfr = [[dyad(x, k_sig) for x in row] for row in sig_fl[name]]
        Mfr, d, tries = repair_psd(name, Mfr, k_sig)
        shifts[name] = d
        sig_dy[name] = Mfr
        print(f"[psd  ] {name}（{len(Mfr)}×{len(Mfr)}，粒度 2^-{k_sig}）："
              f"δ = {float(d):.3e}，LDLᵀ 正定 ✓（{tries} 次）", flush=True)

    # ---- 精确残差 ----
    sv = slack_vec(em, h_dy, e_dy, F_dy)
    ov = sos_vec(em, B_dy)
    resid = [x - y for x, y in zip(sv, ov)]
    R1 = sum(abs(x) for x in resid)
    lhs = minorant_lhs(em, sig_dy)
    rhs = minorant_rhs(em, h_dy)
    rsig = [x - y for x, y in zip(rhs, lhs)]
    R2 = abs(rsig[0]) + B_W * sum(abs(x) for x in rsig[1:])
    print(f"[resid] ‖resid_slack‖₁ = {float(R1):.6e}（max "
          f"{float(max(abs(x) for x in resid)):.2e}）；"
          f"R2 = {float(R2):.6e}（max {float(max(abs(x) for x in rsig)):.2e}）",
          flush=True)

    # ---- 逐点抽查（随机有理 Gram 三点 / 有理 t）----
    rng = random.Random(97531 + k)
    spot = {"sos": None, "resid": None, "minorant": None}
    oks, tries = 0, 0
    while tries < 40 and oks < 8:
        tries += 1
        x = rational_point(Fraction(rng.randint(-64, 64), 64),
                           Fraction(rng.randint(-64, 64), 64))
        y = rational_point(Fraction(rng.randint(-64, 64), 64),
                           Fraction(rng.randint(-64, 64), 64))
        z = rational_point(Fraction(rng.randint(-64, 64), 64),
                           Fraction(rng.randint(-64, 64), 64))
        u = sum(x[i] * y[i] for i in range(3))
        v = sum(x[i] * z[i] for i in range(3))
        t = sum(y[i] * z[i] for i in range(3))
        if not (A_EXACT <= u <= 1 and A_EXACT <= v <= 1 and A_EXACT <= t <= 1):
            continue
        detg = F1 + 2 * u * v * t - u * u - v * v - t * t
        if detg < 0:
            continue
        oks += 1
        # SOS(pt) ≥ 0 精确（B_r ⪰ 0、g_r(pt) ≥ 0 的实例复核）
        sos_pt = F0
        for name, gnz, mons in em.sos_blocks:
            B = B_dy[name]
            m = len(mons)
            zp = []
            for e2 in mons:
                zp.append((u ** e2[0]) * (v ** e2[1]) * (t ** e2[2]))
            quad = sum(B[p][q] * zp[p] * zp[q] for p in range(m) for q in range(m))
            g = sum(c * (u ** eg[0]) * (v ** eg[1]) * (t ** eg[2]) for eg, c in gnz)
            if g < 0:
                fail(f"抽查乘子负值：g_{name}(pt) = {g} < 0（域条件被破坏？）")
            sos_pt += g * quad
        if sos_pt < 0:
            fail(f"SOS 抽查负值：SOS(pt) = {sos_pt} < 0（B_r PSD 机制失败）")
        # slack(pt) = SOS(pt) + resid(pt) 精确一致（系数↔求值两条路）
        slack_pt = em.eval3(sv, u, v, t)
        resid_pt = em.eval3(resid, u, v, t)
        if slack_pt - sos_pt != resid_pt:
            fail("slack(pt) − SOS(pt) ≠ resid(pt)：系数与求值路径不一致")
        if slack_pt < -R1:
            fail(f"slack 抽查 < −R1：{slack_pt} < {-R1}")
        spot["sos"] = dict(checked=oks, all_nonneg=True)
        spot["resid"] = dict(checked=oks, exact_consistent=True)
    if oks == 0:
        fail("随机有理 Gram 三点抽查：40 次尝试未取到 8 个域内点")
    # minorant：(2−2t)·H(t)² ≤ (1+R2)² 于有理 t ∈ [−9/10, 1)（H<0 时自动成立）
    mk = 0
    for t in [A_EXACT, Fraction(-3, 4), Fraction(-1, 2), Fraction(-1, 4), F0,
              Fraction(1, 4), Fraction(1, 2), Fraction(3, 4),
              Fraction(7, 8), Fraction(31, 32), Fraction(995, 1000)]:
        Ht = F0
        tp = F1
        for j in range(em.d_H + 1):
            Ht += h_dy[j] * tp
            tp *= t
        if Ht <= 0:
            mk += 1
            continue
        lhs2 = (2 - 2 * t) * Ht * Ht
        if lhs2 > (1 + R2) ** 2:
            fail(f"minorant 抽查失败：(2−2t)H² = {float(lhs2):.6e} > "
                 f"(1+R2)² = {float((1 + R2) ** 2):.6e} @t = {float(t)}")
        mk += 1
    spot["minorant"] = dict(checked=mk, all_ok=True)

    # ---- 界值与断言 ----
    if e_dy - 36 * R1 <= 0:
        fail(f"e − 36·R1 = {e_dy - 36 * R1} ≤ 0")
    certified = (e_dy - 36 * R1) / (1 + R2)
    if certified <= LP_RECORD:
        fail(f"certified = {float(certified):.12f} ≤ 纪录线 {float(LP_RECORD):.12f}"
             f"（舍入损失吃掉全部收益，粒度 2^-{k} 不合格）")
    if not (0 < certified <= E_star + PHI_TOL):
        fail(f"违反 0 < certified ≤ E*+1e-6：{float(certified):.15e}")
    print(f"[assert] certified > 纪录线 {float(LP_RECORD):.12f} ✓ 且 ≤ E* + 1e-6 ✓"
          f"（E* − certified = {float(E_star - certified):.9f}）"
          f"（认证链 {time.time() - t0:.0f}s）", flush=True)
    return h_dy, e_dy, F_dy, B_dy, sig_dy, shifts, R1, R2, rsig, certified, spot


if __name__ == "__main__":
    main()
