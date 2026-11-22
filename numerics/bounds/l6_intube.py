#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""l6_intube.py — KLT §7.4 Hessian 分解的 N=9 严格化：TTP 管内二次增长（账本 L6 管内半件）。

Round 6 / R6-6（架构 C-混合，notes/architecture-decision.md §3）；R7-3 引入
K-lift 一阶＋二阶分解；**R8-3（本版 /2）**：修复 BD 二阶传播双 bug（R7-3 的
BD2 box 通道因此证书无效，见 decisions D23 裁决 0）＋二阶余项改用 σ_max(J₂)
提升通道的 (1−t) 窗口积分（方向耦合保留）——r* 0.006718398305 → 0.00950125
（≥0.0084 硬阈，=0.0095 stretch）。原始任务：把 tube.json 里"公式值非严格"的
r_tube=0.07601 换成区间算术证书，或如实报告可达的严格半径。本文件诚实交付：
**可达严格半径 ≪ 0.07601**（见 verdict/reconciliation），0.07601 按本方法不可
严格化——原因与定量对账写入 JSON。

============================================================ 数学（全部区间可验证）

**KLT §7.4 分解（s=1, p=1/2）**：E=Σ_{i<j} f_e^{−1/2}，f_e=|x_i−x_j|²。逐边微分
    D²E[v,v] = Σ_e [(3/4) f_e^{−5/2} (D f_e[v])² − (1/2) f_e^{−3/2} D² f_e[v,v]]，
D f_e[v]=2 d_e·Δv_e、D²f_e[v,v]=2|Δv_e|²（常数）——**从不需要 D³E**。加球面约束
曲率项（(S²)⁹ 第二基本形式，测地线 γ̈_i=−|γ̇_i|²y_i）：
    Hess_Y(w,w) = Σ_e [3 f_e^{−5/2}(d_e·Δw_e)² − f_e^{−3/2}|Δw_e|²] − Σ_i μ_i(Y)|w_i|²，
μ_i(Y)=∇_iE·y_i = −½ Σ_{j≠i} 1/r_ij（闭式，本文件区间复核）。

**KLT 分解常数逆境（如实入账的负结果）**：任务书的
    μ_KLT = (3/4) f_min^{−5/2} λ − (1/2) M Σ_e f_{e,min}^{−3/2} + c_curv
在 p=1/2 结构性不利（大 s 时正项 f^{−p−2} 主导，p=1/2 不然）：正项系数
(3/4)f_min^{−5/2}~0.5，而 (1/2)MΣf^{−3/2}~40（36 边、每边 M=4）。本文件逐分箱
区间计算 μ_KLT(r)（全部 ≤ 0，如实报告）。

**可严格化的路线（本证书）——固定坐标输运 Hessian 的扰动界**：
参考构型 X̄=X(z_c)（z_c=自隔离 z* 区间中点，宽度 1e-10，⊆ R1 存档区间）。
固定正交切基 {b_c}（18 维系数空间欧氏）。指数图 χ_{X̄}(v)、传输切映射
（s₁=sinτ/τ、s₂=(cosτ−s₁)/τ² 为 q=τ² 的偶函数幂级数＋严格余项，无 0 除）：
    dχ_v[u]_i = s₁ u + s₂ (v·u) v − s₁ (v·u) x̄_i 。
M(v) := dχ_v^* Hess_{χ(v)}E dχ_v（18×18 区间；v-箱上稀疏对偶区间求值＋**中值形式**
M(v) ⊆ M(0)+Σ_k ∂_kM([box])·v_k，逐元素 Cauchy–Schwarz）；Ĝ(v):=dχ_v^*dχ_v。

对 ‖v‖ ≤ ρ_geo(r)：=2arcsin(r/2)、u ∈ T₀ 且 u ⊥ R̃(v)（旋转子空间拉回）：
    uᵀM(v)u ≥ uᵀM(0)u − ‖Δ_M‖‖u‖² ≥ [λ₀(1−ε_dr²) − 2σε_dr − ‖Δ_M‖]‖u‖²，
    ‖dχ_v[u]‖² = uᵀĜ(v)u ≤ (1+Δ_G)‖u‖²
    ⟹ μ(r) := [λ₀(1−ε_dr²) − 2σε_dr − ‖Δ_M‖_F]/(1+Δ_G) − cross(r)
    ⟹ Hess_{χ(v)}(w,w) ≥ μ(r)‖w‖²  (∀ w ⊥ R(χ(v)))。
λ₀ = M(0) 在 N₀（C_R 的 15 维补基）上的区间 Cholesky 下界；ε_dr=旋转子空间漂移
（拉回场 m_a=dχ_v^*[e_a×ỹ] vs r_a=e_a×x̄ 的区间差＋旋转 Gram 下界）；σ =
sup_{rot}‖M(0)r‖（临界性残差 ∝|E'|）。

**二次增长（沿线段积分，旋转用 Procrustes 最优匹配消去）**：对弦距
d(Y)=min_Q‖Y−QX̄‖ ≤ r* 的 Y：取 Procrustes 全局最优 Q*（Σy·Qx 的 SO(3) 最大点
⟹ 驻点 ⟹ Σy_i×x'_i=0，advisory 复核 1e-16），测地线 γ(t)=χ_{X'}(t·w)，
w_i=(y_i−cosτ_i x'_i)(τ_i/sinτ_i)（测地线初速，切向）。角动量
L(t)=Σγ_i×γ̇_i=Σx'_i×w_i 常量，且
    |L₀| ≤ max_i|τ/sinτ−1|·Σsinτ_i ≤ (ρ_geo²/6)·3ρ_geo = ρ_geo³/2（区间）
⟹ 旋转分量 |ω(t)| ≤ |L₀|/λ_min(rotGram≥5.6) = O(r³)；交叉项
|2Hess(u,ρ)|+|Hess(ρ,ρ)| = |dE(2∇_uρ+∇_ρρ)| ≤ (2|ω|+6|ω|²)‖∇E‖ =: cross。
临界性残差 γ_res=‖切向∇E(X̄)‖（z 隔离 1e-10 ⟹ ~1e-8）。对 t 积分
E(Y)−Ē = h'(0)+∫₀¹(1−t)h''(t)dt 得
    E(Y) ≥ Ē − γ_res·d(Y) + (μ/2)d(Y)²，Ē=E(X̄)（区间）。
竞争者陷阱：E(Y) ≤ Ē ⟹ d(Y) ≤ 2γ_res/μ（r* 球内）。

**刚性组件（KLT 引理 7.1 TTP 版）**：ν₆（内积 0.3553 的 12 条短边）单独**不可能**
无穷小刚性——行数 12 < 15 = 2·9−3（Maxwell 计数，纯数学；数值 rank 12、核 6 维=
3 旋转+3 挠曲）。增广集 S*=ν₆∪ν₂（18 边）：rank 15、核恰为 SO(3)（旋转在核中=
精确恒等式 (d)·(ω×d)=0 区间复核；N₀ 上 λ_S>0 排除非旋转核）＋**严格正自应力**
（S* 全 1 权重：每顶点 Σ±d_e = 3x_T / 6x_C 精确法向平衡，区间残差复核）；全 36
边图有解析正自应力 ω_e=f_e^{−3/2}（=临界性恒等式=D²E 负项系数）。λ_S(r)（S*
未加权刚性 Gram 商空间最小特征值）管上分箱区间赋值＝任务组件 (2)。

【组件清单↔任务书】(1) 刚性+自应力=§rigidity；(2) λ 管上分箱区间=§bins.lambdaS；
(3) f_e 区间+M=§bins.fMin/fMax/M；(4) μ 合成+积分=§bins.mu+§quadraticGrowth；
μ_KLT 任务原式=§bins.muKltSplit（负结果如实）。

【门】①固定参数重算与存档逐位一致（先跑写档、再跑比对）；②μ>0 ⟺
rigorous_tube_radius>0 内部一致；③负对照五件（R8-3 起第五件为联合通道专属）：
管半径加倍（R_MAX=2×0.07601）⇒μ≤0；自应力权重改非正（Gram 权重 (1,−1) /
符号翻转）⇒刚性下界必失败；μ 符号翻转 ⇒下游增长断言必检；二阶通道换回
标量方向解耦 ⇒ r* 必回退旧档及以下（提升通道被实际使用）。
【门（R8-3 增）】bd_rules_selftest：BD 二阶传播规则 vs 解析 r⁻¹/r⁻⁵ 有限差分
逐键对照，每次运行强制（R7-3 规则 bug 的回归门）。验收门 r8_l6_gate.py。

用法：python3 numerics/bounds/l6_intube.py [--out PATH]
依赖：mpmath>=1.3（区间算术）；numpy（仅 advisory，不入信任链）。
确定性：无时间戳/运行时字段；固定阶梯常数；固定种子 20261006；sort_keys 序列化。
"""
from __future__ import annotations

import argparse
import json
import math
import random
import sys
import time
from pathlib import Path

import mpmath
from mpmath import iv, mp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import local_min as lm  # noqa: E402  R1 已验证的 E/E'/E'' 区间机器

# ------------------------------------------------------------------ 配置（固定）
IV_DPS = 40
MP_DPS = 70
SEED = 20261006
CODE_VERSION = "l6-intube/2"
# R8-3 提升（lift）通道参数（固定、确定性）
K_LIFT_MAX_BIN = 34               # 提升通道适用箱上限（r=0.015979134；更大箱沿用 legacy）
LIFT_J = 10                       # δ-阶梯步数（δ_j = j·DLIFT/LIFT_J，含 δ_0=0）
LIFT_PITER = 160                  # σ_max 认证的 float 幂迭代步数（定方向用）
R73_ARCHIVE = {"klam_slope": "12.83599046", "d2op_box": "2016.729948",
               "r_star": "0.006718398305",
               "mu_at_rstar": "[0.011934442525868117, 0.011934490133085328]"}
Z_ISO_WIDTH = "1e-10"            # 自隔离 z* 目标宽度（比 R1 存档 1e-6 细）
K_BINS = 48                      # 固定分箱数（四分之一倍频程，比率 2^{1/4}）
LAMBDA0_LADDER = ("0.1439", "0.14385", "0.1438", "0.1437", "0.1435", "0.143",
                  "0.142", "0.14", "0.13", "0.12", "0.10", "0.08", "0.05",
                  "0.02", "0.01")
LAMBDA_S_LADDER = ("0.335", "0.33", "0.32", "0.31", "0.30", "0.28", "0.25",
                   "0.2", "0.15", "0.1", "0.05", "0.02", "0.01")
N_SER = 6                        # s₁/s₂/cos 的 q-幂级数项数（余项 ~1e-18）
DELTA_E_CAP = "0.00041534539928310784"   # E*−certified(m0748_M8)（tube.json meta）
LAMBDA_REF_FLM = "0.14378982"             # full_local_min.json λ 区间下界
R_TARGET_FORMULA = "0.07601"              # sqrt(2ΔE/λ_ref) 公式值（tube.json）
R_TOL = "1e-5"

RESULTS = HERE / "results"
DEFAULT_OUT = RESULTS / "l6_intube.json"

iv.dps = IV_DPS
mp.dps = MP_DPS
_0 = iv.mpf(0)
_1 = iv.mpf(1)
T0WALL = time.time()

PTS_RHO = None     # (pts, rho)：X̄ 的区间 9 点与 ρ（run_certificate 设置）
BAS = None         # 18 列 (point_idx, interval 3-vec) 固定正交切基


class CheckError(Exception):
    """验证断言失败（负对照按预期触发也用它携带原因）。"""


def require(cond, msg: str) -> None:
    if not cond:
        raise CheckError(msg)


def istr(I) -> str:
    return f"[{mp.nstr(mp.mpf(I.a), 17)}, {mp.nstr(mp.mpf(I.b), 17)}]"


def isup(I) -> mp.mpf:
    return max(abs(mp.mpf(I.a)), abs(mp.mpf(I.b)))


def contains_zero(I) -> bool:
    return mp.mpf(I.a) <= 0 <= mp.mpf(I.b)


def f2s(x) -> str:
    """确定性浮点串（advisory 专用，10 位）。"""
    return f"{float(x):.10g}"


def _sq_iv(I):
    a, b = mp.mpf(I.a), mp.mpf(I.b)
    return iv.mpf([min(a * a, b * b), max(a * a, b * b)])


# ================================================================ 区间线性代数（与 full_local_min 同实现，已验证）
def interval_cholesky_pd(A, label: str):
    n = len(A)
    L = [[_0] * n for _ in range(n)]
    d = [None] * n
    for j in range(n):
        s = A[j][j]
        for k in range(j):
            s = s - d[k] * (L[j][k] * L[j][k])
        if mp.mpf(s.a) <= 0:
            raise CheckError(f"{label}: pivot {j} not positive definite, interval {istr(s)}")
        d[j] = s
        inv = _1 / s
        for i in range(j + 1, n):
            t = A[i][j]
            for k in range(j):
                t = t - d[k] * (L[i][k] * L[j][k])
            L[i][j] = t * inv
    return d


def mp_cholesky_upper(A, label: str):
    n = len(A)
    R = [[mp.mpf(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            s = A[i][j]
            for k in range(i):
                s = s - R[k][i] * R[k][j]
            if i == j:
                if s <= mp.mpf("1e-30"):
                    raise CheckError(f"{label}: preconditioner pivot {i} not PD ({mp.nstr(s, 6)})")
                R[i][i] = mp.sqrt(s)
            else:
                R[i][j] = s / R[i][i]
    return R


def mp_upper_inverse(R):
    n = len(R)
    Ri = [[mp.mpf(0)] * n for _ in range(n)]
    for i in range(n - 1, -1, -1):
        Ri[i][i] = 1 / R[i][i]
        for j in range(i + 1, n):
            Ri[i][j] = -sum(R[i][l] * Ri[l][j] for l in range(i + 1, j + 1)) / R[i][i]
    return Ri


def certify_pd_preconditioned(X_enc, label: str):
    n = len(X_enc)
    R = mp_cholesky_upper([[(mp.mpf(X_enc[i][j].a) + mp.mpf(X_enc[i][j].b)) / 2
                            for j in range(n)] for i in range(n)], label + " [precond]")
    Ri = mp_upper_inverse(R)
    B = [[iv.mpf(mp.nstr(Ri[i][j], 60)) for j in range(n)] for i in range(n)]
    Y = [[sum((X_enc[i][k] * B[k][l] for k in range(n)), _0) for l in range(n)]
         for i in range(n)]
    Xt = [[sum((B[k][i] * Y[k][j] for k in range(n)), _0) for j in range(n)]
          for i in range(n)]
    interval_cholesky_pd(Xt, label + " [congruence]")


def certify_lambda(A, ladder, label):
    """A（n×n 区间）− λI ≻ 0 的最大阶梯 λ（阶梯固定常数，确定性）。"""
    n = len(A)
    for lam in ladder:
        L = iv.mpf(lam)
        try:
            certify_pd_preconditioned(
                [[A[a][b] - (L if a == b else _0) for b in range(n)] for a in range(n)],
                f"{label} (lambda={lam})")
            return L
        except CheckError:
            continue
    raise CheckError(f"{label}: no ladder value certified")


# ================================================================ 稀疏对偶区间（BD，R7-3 起带可选二阶）
def _ddkey(i, j):
    return (i, j) if i <= j else (j, i)


def _ddget(dd, i, j):
    return dd.get(_ddkey(i, j), None)


class BD:
    """(value, {key: ∂/∂v_key}, {(i,j)≤: ∂²/∂v_i∂v_j})：稀疏前向 AD＋区间 enclosure。

    dd=None 表示未携带二阶导（旧路径，零开销）；dd={} 表示全零二阶导（BD2 种子）。
    二阶传播规则（Hessian 键 k≤l；R8-3 修复版，bd_rules_selftest 逐次运行复核）：
      (uv)''_{kl} = u''_{kl}v + u v''_{kl} + u'_k v'_l + u'_l v'_k（乘积梯度交叉）；
      (√u)''_{kl} = u''_{kl}/(2√u) − u'_k u'_l/(4u^{3/2})（对称平方：每个无序键恰一次）；
      (u/v)''_{kl} = u''_{kl}/v − (u'_k v'_l + u'_l v'_k)/v² − u v''_{kl}/v²
                     + 2u v'_k v'_l/v³（末项分母 b³，无序键恰一次）。
    R7-3 存档版本有两处 bug（bsqrt 第二项对角/交叉 ×2；bdiv 末项 a.v/b² 应为
    a.v/(2·b³) 且键重复累加），实测 .dd 不含真二阶导数（FD 对照 6/6 出界，含
    符号翻转）——该 bug 使 R7-3 的 BD2 box 通道证书无效（d2op=2016.7 系错误
    张量的包络）；R8-3 修复后同一 box 通道复算 d2op≈866，且 .dd 与解析 FD
    逐位吻合（见 bd_rules_selftest 与 decisions D18）。"""
    __slots__ = ("v", "d", "dd")

    def __init__(self, v, d=None, dd=None):
        self.v = v
        self.d = d if d is not None else {}
        self.dd = dd


def bkonst(x) -> BD:
    return BD(iv.mpf(x))


def bkzero() -> BD:
    return BD(_0)


def bkvar(key, box) -> BD:
    return BD(iv.mpf([mp.mpf(-box), mp.mpf(box)]), {key: _1})


def bkvar2(key, box) -> BD:
    """BD2 种子：box 值＋一阶导 1＋二阶导 0。"""
    return BD(iv.mpf([mp.mpf(-box), mp.mpf(box)]), {key: _1}, {})


def _dd_combine(a: BD, b: BD, sgn: int):
    if a.dd is None and b.dd is None:
        return None
    out = dict(a.dd) if a.dd else {}
    if b.dd:
        for k, v in b.dd.items():
            out[k] = out.get(k, _0) + sgn * v
    return out


def _dd_mul(a: BD, b: BD):
    if a.dd is None and b.dd is None:
        return None
    out = {}
    if a.dd:
        for k, v in a.dd.items():
            out[k] = v * b.v
    if b.dd:
        for k, v in b.dd.items():
            out[k] = out.get(k, _0) + a.v * v
    for i, da in a.d.items():
        for j, db in b.d.items():
            kk = _ddkey(i, j)
            t = da * db
            if i == j:
                t = t + t
            out[kk] = out.get(kk, _0) + t
    return out


def badd(a: BD, b: BD) -> BD:
    d = dict(a.d)
    for k, v in b.d.items():
        d[k] = d.get(k, _0) + v
    return BD(a.v + b.v, d, _dd_combine(a, b, 1))


def bsub(a: BD, b: BD) -> BD:
    d = dict(a.d)
    for k, v in b.d.items():
        d[k] = d.get(k, _0) - v
    return BD(a.v - b.v, d, _dd_combine(a, b, -1))


def bmul(a: BD, b: BD) -> BD:
    d = {}
    for k, v in a.d.items():
        d[k] = v * b.v
    for k, v in b.d.items():
        d[k] = d.get(k, _0) + a.v * v
    return BD(a.v * b.v, d, _dd_mul(a, b))


def bscale(a: BD, c) -> BD:
    c = iv.mpf(c)
    dd = None if a.dd is None else {k: v * c for k, v in a.dd.items()}
    return BD(a.v * c, {k: v * c for k, v in a.d.items()}, dd)


def bdiv(a: BD, b: BD) -> BD:
    d = {}
    for k, v in a.d.items():
        d[k] = v / b.v
    for k, v in b.d.items():
        if k in d:
            d[k] = d[k] - (a.v / (b.v * b.v)) * v
        else:
            d[k] = -(a.v / (b.v * b.v)) * v
    if a.dd is None and b.dd is None:
        dd = None
    else:
        b2 = b.v * b.v
        b3 = b2 * b.v
        dd = {}
        if a.dd:
            for k, v in a.dd.items():
                dd[k] = v / b.v
        if b.dd:
            for k, v in b.dd.items():
                dd[k] = dd.get(k, _0) - a.v * v / b2
        avb3 = a.v / b3
        for i, da in a.d.items():
            for j, db in b.d.items():
                kk = _ddkey(i, j)
                t = -(da * db) / b2
                if i == j:
                    t = t + t
                dd[kk] = dd.get(kk, _0) + t
        _items = list(b.d.items())
        for _ai in range(len(_items)):
            i, db = _items[_ai]
            for j, db2 in _items[_ai:]:
                kk = _ddkey(i, j)
                dd[kk] = dd.get(kk, _0) + 2 * avb3 * db * db2
    return BD(a.v / b.v, d, dd)


def bsqrt(a: BD) -> BD:
    s = iv.sqrt(a.v)
    dd = None
    if a.dd is not None:
        dd = {}
        inv2s = _1 / (2 * s)
        for k, v in a.dd.items():
            dd[k] = v * inv2s
        inv4 = _1 / (4 * s * s * s)
        _items = list(a.d.items())
        for _ai in range(len(_items)):
            i, di = _items[_ai]
            for j, dj in _items[_ai:]:
                kk = _ddkey(i, j)
                dd[kk] = dd.get(kk, _0) - (di * dj) * inv4
    return BD(s, {k: v / (2 * s) for k, v in a.d.items()}, dd)


def bdot3(u, w) -> BD:
    r = bkzero()
    for a, b in zip(u, w):
        r = badd(r, bmul(a, b))
    return r


_FACT = {}


def _fact(n: int):
    if n not in _FACT:
        _FACT[n] = mpmath.factorial(n)
    return _FACT[n]


def _alt_rem(qmax, next_coeff, order):
    """交错递减级数余项 ⊆ ±next_coeff·qmax^order（q ≤ 0.0242 保证单调递减）。"""
    qh = mp.mpf(qmax.b) if hasattr(qmax, "b") else mp.mpf(qmax)
    ch = mp.mpf(next_coeff.b) if hasattr(next_coeff, "b") else mp.mpf(next_coeff)
    t = ch * qh ** order
    return iv.mpf([mp.mpf(-t), mp.mpf(t)])


def series_c(q: BD, qmax) -> BD:
    r = bkonst(_1)
    qk = bkonst(_1)
    for k in range(1, N_SER):
        qk = bmul(qk, q)
        r = badd(r, bscale(qk, iv.mpf((-1) ** k) / iv.mpf(_fact(2 * k))))
    return badd(r, BD(_alt_rem(qmax, 1 / iv.mpf(_fact(2 * N_SER)), N_SER)))


def series_s1(q: BD, qmax) -> BD:
    r = bkonst(_1)
    qk = bkonst(_1)
    for k in range(1, N_SER):
        qk = bmul(qk, q)
        r = badd(r, bscale(qk, iv.mpf((-1) ** k) / iv.mpf(_fact(2 * k + 1))))
    return badd(r, BD(_alt_rem(qmax, 1 / iv.mpf(_fact(2 * N_SER + 1)), N_SER)))


def series_s2(q: BD, qmax) -> BD:
    # s₂ = Σ_{j≥0} (−1)^{j+1} (2j+2)/(2j+3)! q^j
    r = bscale(bkonst(_1), -iv.mpf(2) / iv.mpf(6))
    qk = bkonst(_1)
    for j in range(1, N_SER):
        qk = bmul(qk, q)
        coeff = iv.mpf((-1) ** (j + 1)) * iv.mpf(2 * j + 2) / iv.mpf(_fact(2 * j + 3))
        r = badd(r, bscale(qk, coeff))
    nxt = iv.mpf(2 * N_SER + 2) / iv.mpf(_fact(2 * N_SER + 3))
    return badd(r, BD(_alt_rem(qmax, nxt, N_SER)))


def q_of(vi) -> BD:
    """q = |v_i|² 的 BD（值 + 对偶 2Σv·dv + 二阶 2Σdv_i dv_j）。"""
    qv = vi[0].v * vi[0].v + vi[1].v * vi[1].v + vi[2].v * vi[2].v
    qd = {}
    for t in range(3):
        for k, dv in vi[t].d.items():
            qd[k] = qd.get(k, _0) + vi[t].v * dv
    dd = None
    if any(x.dd is not None for x in vi):
        dd = {}
        for t in range(3):
            for k1, dv1 in vi[t].d.items():
                for k2, dv2 in vi[t].d.items():
                    kk = _ddkey(k1, k2)
                    t2 = dv1 * dv2
                    if k1 == k2:
                        t2 = t2 + t2
                    dd[kk] = dd.get(kk, _0) + t2
    return BD(qv, {k: 2 * v for k, v in qd.items()}, dd)


# ================================================================ 构型、边集与固定基
ROLE = ["T"] * 3 + ["B"] * 3 + ["C"] * 3
PAIRS = [(i, j) for i in range(9) for j in range(i + 1, 9)]
# 结构化边分类（D3h 角度常数的精确后果，无数值聚类）：
E_NU6 = [(0, 6), (0, 8), (1, 6), (1, 7), (2, 7), (2, 8),
         (3, 6), (3, 8), (4, 6), (4, 7), (5, 7), (5, 8)]      # 短边：T/B–C ±60°（12）
E_NU2 = [(0, 7), (1, 8), (2, 6), (3, 7), (4, 8), (5, 6)]      # T/B–C 对顶 180°（6）
E_NU1 = [(0, 4), (0, 5), (1, 3), (1, 5), (2, 3), (2, 4)]      # T–B 斜线 k≠j（6）
E_NU4 = [(0, 3), (1, 4), (2, 5)]                              # T–B 竖边（3）
E_NU5 = [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)]      # T–T/B–B 三角（6）
E_NU3 = [(6, 7), (6, 8), (7, 8)]                              # C–C 三角（3）
S_STAR = E_NU6 + E_NU2                                        # 认证用刚性增广集（18）


def angles_exact():
    h = iv.sqrt(iv.mpf(3))
    half = iv.mpf(1) / 2
    tri = [(iv.mpf(1), _0), (iv.mpf(-1) / 2, h / 2), (iv.mpf(-1) / 2, -h / 2)]
    caps = [(half, h / 2), (iv.mpf(-1), _0), (half, -h / 2)]
    return tri, caps


def ttp_points(Z):
    rho = iv.sqrt(_1 - Z * Z)
    tri, caps = angles_exact()
    pts = ([(rho * c, rho * s, Z) for c, s in tri]
           + [(rho * c, rho * s, -Z) for c, s in tri]
           + [(c, s, _0) for c, s in caps])
    return pts, rho


def tangent_basis_iv(pts):
    cols = []
    for i, p in enumerate(pts):
        sxy = iv.sqrt(p[0] * p[0] + p[1] * p[1])
        e1 = [-p[1] / sxy, p[0] / sxy, _0]
        e2 = [p[1] * e1[2] - p[2] * e1[1],
              p[2] * e1[0] - p[0] * e1[2],
              p[0] * e1[1] - p[1] * e1[0]]
        cols.append((i, e1))
        cols.append((i, e2))
    return cols


# ================================================================ 输运形式装配（核心）
def build_forms(vfun, qmax, sset):
    """M(v)（Hessian 输运形式）、GS(v)（S* 未加权刚性）、Ĝ(v)（度量）：18×18 BD。

    Hess 的曲率项符号：M −= μ_i (W_c·W_c')，μ_i = −½Σ_j 1/r_ij < 0 ⟹ 正贡献。"""
    pts, rho = PTS_RHO
    prep = {}
    for i in range(9):
        vi = vfun(i)
        q = q_of(vi)
        prep[i] = (vi, series_c(q, qmax), series_s1(q, qmax), series_s2(q, qmax))

    def y_of(i):
        vi, c, s1, s2 = prep[i]
        return [badd(bmul(c, bkonst(pts[i][t])), bmul(s1, vi[t])) for t in range(3)]

    def w_of(i, cidx):
        vi, c, s1, s2 = prep[i]
        u = BAS[cidx][1]
        vu = bdot3(vi, [bkonst(u[t]) for t in range(3)])
        out = []
        for t in range(3):
            term = bscale(s1, u[t])
            term = badd(term, bmul(bmul(s2, vu), vi[t]))
            term = bsub(term, bmul(bmul(s1, vu), bkonst(pts[i][t])))
            out.append(term)
        return out

    ycache = {i: y_of(i) for i in range(9)}
    colmap = {}
    for cidx, (i, _u) in enumerate(BAS):
        colmap.setdefault(i, []).append(cidx)
    wcache = {(i, c): w_of(i, c) for i in range(9) for c in colmap[i]}

    M = [[bkzero() for _ in range(18)] for _ in range(18)]
    GS = [[bkzero() for _ in range(18)] for _ in range(18)]
    Gh = [[bkzero() for _ in range(18)] for _ in range(18)]
    mu_sum = {i: bkzero() for i in range(9)}
    f_vals = {}

    for (i, j) in PAIRS:
        yi, yj = ycache[i], ycache[j]
        d = [bsub(yi[t], yj[t]) for t in range(3)]
        r2 = bdot3(d, d)
        r = bsqrt(r2)
        r3 = bdiv(bkonst(_1), bmul(r, r2))
        r5 = bdiv(r3, r2)
        f_vals[(i, j)] = r2.v
        inv_r = bdiv(bkonst(_1), r)
        mu_sum[i] = bsub(mu_sum[i], bscale(inv_r, iv.mpf("0.5")))
        mu_sum[j] = bsub(mu_sum[j], bscale(inv_r, iv.mpf("0.5")))
        cols = colmap[i] + colmap[j]
        dW, dD = {}, {}
        for c in cols:
            pc = BAS[c][0]
            wc = wcache[(pc, c)]
            if pc == i:
                dW[c] = list(wc)
            else:
                dW[c] = [bscale(x, -1) for x in wc]
            dD[c] = bdot3(d, dW[c])
        in_s = (i, j) in sset
        for ai, c in enumerate(cols):
            for c2 in cols[ai:]:
                wc = bdot3(dW[c], dW[c2])
                term = bsub(bmul(bmul(bkonst(iv.mpf(3)), bmul(dD[c], dD[c2])), r5),
                            bmul(wc, r3))
                M[c][c2] = badd(M[c][c2], term)
                if in_s:
                    GS[c][c2] = badd(GS[c][c2], bmul(dD[c], dD[c2]))
    # 镜像
    for a in range(18):
        for b in range(a):
            M[a][b] = M[b][a]
            GS[a][b] = GS[b][a]
            Gh[a][b] = Gh[b][a]
    # 曲率项＋输运度量 Ĝ（逐点 2×2 块；Ĝ_cc' = Σ_i W_c,i·W_c',i）
    for i in range(9):
        cols = colmap[i]
        for ai, c in enumerate(cols):
            for c2 in cols[ai:]:
                wc = bdot3(wcache[(i, c)], wcache[(i, c2)])
                M[c][c2] = bsub(M[c][c2], bmul(mu_sum[i], wc))
                Gh[c][c2] = badd(Gh[c][c2], wc)
    for a in range(18):
        for b in range(a):
            M[a][b] = M[b][a]
    return M, GS, Gh, {i: mu_sum[i].v for i in range(9)}, f_vals


def vfun_point(_i):
    return (bkzero(), bkzero(), bkzero())


def vfun_box(R):
    def f(i):
        return tuple(bkvar(3 * i + t, R) for t in range(3))
    return f


def vfun_point_deriv(i):
    """v=0 处的种子导数：值 0、∂=1 —— 给出 sharp 的 ∂_kM(0)（K-lift 用）。"""
    return tuple(BD(_0, {3 * i + t: _1}) for t in range(3))


def vfun_box2(R):
    """BD2 种子：box 值＋一阶＋二阶全零 —— 给出 sup|∂²_kl M(box)|（Taylor 余项用）。"""
    def f(i):
        return tuple(bkvar2(3 * i + t, R) for t in range(3))
    return f


def vfun_fixed(vflat):
    """固定点 v 的取值器（值=定点、无导数）：M(v) 点值（advisory 交叉核对用）。"""
    def f(i):
        return tuple(BD(iv.mpf(vflat[3 * i + t])) for t in range(3))
    return f


# ================================================================ R7-3：K-lift 一阶项认证
def klift_cert(M0dB, iters=120):
    """sup_{‖u‖=1} ‖(u^T A_k u)_k‖₂ 的严格上界（A_k = ∂_kM(0) 区间矩阵）。

    Σ_k(u^TA_ku)² = vec_sym(uu^T)^T K vec_sym(uu^T)，‖vec_sym(uu^T)‖_F = 1
    ⟹ sup ≤ λ_max(K)，K = J^TJ（J[k,α] = A_k 的对称半向量化；α=(i≤j)，对角原值、
    非对角 ×√2）。λ_max 用区间 Ritz：对称 A、单位 y、θ=y^TAy、r=Ay−θy
    ⟹ λ_max ≤ θ_hi + 2‖r‖sup（x^T(A−θyy^T)x=0 ⟹ ‖A−θyy^T‖≤2‖r‖）。"""
    n = 18
    pairs_idx = [(i, j) for i in range(n) for j in range(i, n)]
    m = len(pairs_idx)
    keys = sorted({k for a in range(n) for b in range(a, n) for k in M0dB[a][b].d})
    # J 行（k）列（α）：区间
    Jm = [[None] * m for _ in range(len(keys))]
    for ai, key in enumerate(keys):
        for a_, (i, j) in enumerate(pairs_idx):
            e = M0dB[i][j].d.get(key)
            if e is None:
                e = M0dB[j][i].d.get(key)
            if e is None:
                e = _0
            sc = _1 if i == j else iv.sqrt(iv.mpf(2))
            Jm[ai][a_] = e * sc
    # K = J^T J（区间矩阵 171×171）
    K = [[_0] * m for _ in range(m)]
    for a_ in range(m):
        for b_ in range(a_, m):
            s = _0
            for ai in range(len(keys)):
                s = s + Jm[ai][a_] * Jm[ai][b_]
            K[a_][b_] = s
            K[b_][a_] = s
    # float 中点幂迭代（定向用，不承担证明）
    Kf = [[(mp.mpf(K[i][j].a) + mp.mpf(K[i][j].b)) / 2 for j in range(m)] for i in range(m)]
    y = [mp.mpf(1)] + [mp.mpf(0)] * (m - 1)
    for _ in range(iters):
        z = [sum((Kf[i][j] * y[j] for j in range(m)), mp.mpf(0)) for i in range(m)]
        nz = mp.sqrt(sum((v * v for v in z), mp.mpf(0)))
        if nz == 0:
            break
        y = [v / nz for v in z]
    yv = [iv.mpf(mp.nstr(v, 40)) for v in y]
    s2 = sum((_sq_iv(v) for v in yv), _0)
    theta = sum((yv[a_] * sum((K[a_][b_] * yv[b_] for b_ in range(m)), _0)
                 for a_ in range(m)), _0) / s2
    r2 = _0
    for j in range(m):
        acc = sum((K[j][a_] * yv[a_] for a_ in range(m)), _0) - theta * yv[j]
        r2 = r2 + _sq_iv(acc)
    lam_hi = (theta + iv.mpf(2) * iv.sqrt(r2)) / s2 * iv.mpf("1.000000000000001")
    klam = iv.sqrt(lam_hi if mp.mpf(lam_hi.a) > 0 else
                   iv.mpf([mp.mpf(0), mp.mpf(lam_hi.b)]))
    info = dict(
        method="symmetric-Kronecker lift J^TJ（rank-1 松弛 λ_max）+ 区间 Ritz",
        dim=m, n_derivs=len(keys),
        lam_max=mp.nstr(mp.mpf(lam_hi.b), 10),
        klam_slope=mp.nstr(mp.mpf(klam.b), 10),
        note="一阶项 dM₁ = R·√λ_max(K)：对 ‖v‖≤R 一致（CS 于 (A_k(0),v_k) 联合）")
    return klam, info


def taylor_d2_pass(Rbox):
    """sup|∂²_kl M| over box → D2mat（模 CS）→ op 范数（legacy BD2 通道，留档对照）。"""
    M2, GS2, Gh2, mu2, fv2 = build_forms(vfun_box2(Rbox), iv.mpf(Rbox * Rbox), set(S_STAR))
    n = 18
    cssq = [[_0] * n for _ in range(n)]
    dd_count = 0
    maxsup = mp.mpf(0)
    for a in range(n):
        for b in range(a, n):
            dd = M2[a][b].dd or {}
            for (k, l), v in dd.items():
                sup = max(abs(mp.mpf(v.a)), abs(mp.mpf(v.b)))
                maxsup = max(maxsup, sup)
                w = _1 if k == l else iv.mpf(2)
                cssq[a][b] = cssq[a][b] + w * _sq_iv(v)
            dd_count += len(dd)
    for a in range(n):
        for b in range(a):
            cssq[a][b] = cssq[b][a]
    D2 = [[iv.sqrt(cssq[a][b]) for b in range(n)] for a in range(n)]
    d2op = op_norm_bound(D2)
    info = dict(
        r2box=mp.nstr(mp.mpf(Rbox), 10),
        dd_entries=dd_count, max_sup_d2=mp.nstr(maxsup, 8),
        d2_modcs_opnorm=mp.nstr(mp.mpf(d2op.b), 10),
        note="legacy BD2 box 通道（区间依赖宽度放大 ~8×，仅对照保留）")
    return d2op, info


# ================================================================ R7-3：二阶余项的逐边联合界（无 box）
def joint_second_order(Rbox):
    """REM = M(v)−M(0)−DM(0)[v] 于 ‖v‖≤Rbox 的联合界（积分形式）。

    恒等式：M(v)−M(0) = DM(0)[v] + ∫₀¹(1−t)·(d²/dt²)M(tv)dt（一阶项由 K-lift
    单独认证）。逐边对 G_e = 3r⁻⁵D² − r⁻³|W|² 与曲率 −μ_i|w_i|² 做二阶 t 导数的
    闭式标量界（全部用 r 的点值区间＋|d′|、|d″|、|w′|、|w″| 球半径界——**不做
    box AD**，规避 1/r⁵ 链的区间依赖放大），每个被乘 (s_ui+s_uj)² 或 s_ui² 的
    u-二次型（PSD：2(P_i+P_j) / P_i，系数空间），合并为 Ĝ 后 dM₂ = ½·op_norm(Ĝ)。"""
    n = 9
    pts, _rho = PTS_RHO
    R = mp.mpf(Rbox)
    # —— 球半径闭式界（对 ∀t∈[0,1]、∀‖v‖≤R 一致）——
    b1 = R * (1 + R / 6 + R ** 2 / 4)          # |d/dt y_i(tv)| ≤ b1（逐点）
    b2 = R ** 2 * (1 + R + R ** 2 / 3)         # |d²/dt² y_i(tv)| ≤ b2
    a1 = R * (1 + R / 2 + R ** 2 / 4)          # |d/dt w_i(tv)| ≤ a1·|u_i|
    a2 = R ** 2 * (1 / 2 + R)                  # |d²/dt² w_i(tv)| ≤ a2·|u_i|
    Dp = iv.mpf(2 * b1)                        # |d′|（边两端）
    Dpp = iv.mpf(2 * b2)
    Wp_c = iv.mpf(a1)                          # |W′| ≤ a1·(Δs)
    Wpp_c = iv.mpf(a2)
    # 系数空间 PSD 矩阵（区间）：P_i[c][c'] = δ_cc'·Σ_t u_c[t]²（c 属于点 i 的块）
    Pis = []
    for i in range(n):
        Mx = [[_0] * 18 for _ in range(18)]
        for c, (ci, u) in enumerate(BAS):
            if ci == i:
                s2 = sum((_sq_iv(u[t]) for t in range(3)), _0)
                Mx[c][c] = s2
        Pis.append(Mx)
    Gtil = [[_0] * 18 for _ in range(18)]
    edge_weights = []
    for (i, j) in PAIRS:
        dbar = [pts[i][t] - pts[j][t] for t in range(3)]
        rbar = iv.sqrt(sum((_sq_iv(x) for x in dbar), _0))
        rlo = rbar - Dp
        require(mp.mpf(rlo.a) > 0, f"joint_second_order: r_lo <= 0 on edge ({i},{j})")
        rlo_inv2 = _1 / (rlo * rlo)
        rlo_inv4 = _1 / (rlo * rlo * rlo * rlo)
        rlo_inv5 = iv.mpf(1) / iv.power(rlo, iv.mpf(5))
        rlo_inv6 = iv.mpf(1) / iv.power(rlo, iv.mpf(6))
        rlo_inv7 = iv.mpf(1) / iv.power(rlo, iv.mpf(7))
        Dsup = rbar + Dp
        g5sup = iv.mpf(1) / iv.power(rlo, iv.mpf(5))
        g3sup = iv.mpf(1) / iv.power(rlo, iv.mpf(3))
        g5p = iv.mpf(5) / iv.power(rlo, iv.mpf(6)) * Dp
        g3p = iv.mpf(3) * rlo_inv4 * Dp
        g1p = rlo_inv2 * Dp
        g5pp = iv.mpf(35) * Dp * Dp * rlo_inv7 + iv.mpf(5) * Dpp * rlo_inv7
        g3pp = iv.mpf(15) * Dp * Dp * rlo_inv5 + iv.mpf(3) * Dpp * rlo_inv4 / rlo
        g1pp = iv.mpf(4) * Dp * Dp * rlo_inv4 + Dpp * rlo_inv4
        Wsup_c = iv.mpf(1) + Wp_c                       # ×(Δs)
        # |D|,|D′|,|D″| ≤ (…)(Δs)
        Dsup_c = Dsup * Wsup_c
        Dp_c = Dp * Wsup_c + Dsup * Wp_c
        Dpp_c = Dpp * Wsup_c + iv.mpf(2) * Dp * Wp_c + Dsup * Wpp_c
        # d²/dt²[3 g⁵ D²] 的界（×(Δs)²）
        w_edge = (iv.mpf(3) * (g5pp * _sq_iv(Dsup_c)
                               + iv.mpf(4) * g5p * Dsup_c * Dp_c
                               + g5sup * (iv.mpf(2) * _sq_iv(Dp_c)
                                          + iv.mpf(2) * Dsup_c * Dpp_c))
                  + g3pp * _sq_iv(Wsup_c)
                  + iv.mpf(4) * g3p * Wsup_c * Wp_c
                  + g3sup * (iv.mpf(2) * _sq_iv(Wp_c)
                             + iv.mpf(2) * Wsup_c * Wpp_c))
        edge_weights.append(mp.mpf(w_edge.b))
        w2 = w_edge * iv.mpf(2)                         # (Δs)² ≤ 2u^T(P_i+P_j)u
        for a in range(18):
            for b in range(18):
                Gtil[a][b] = Gtil[a][b] + w2 * (Pis[i][a][b] + Pis[j][a][b])
    # 曲率项：d²/dt²[−μ_i|w_i|²]，μ_i = −½Σ_j 1/r_ij < 0
    for i in range(n):
        mu_sup = _0
        mu_p = _0
        mu_pp = _0
        for (p, q) in PAIRS:
            if p != i and q != i:
                continue
            dbar = [pts[p][t] - pts[q][t] for t in range(3)]
            rbar = iv.sqrt(sum((_sq_iv(x) for x in dbar), _0))
            rlo = rbar - Dp
            mu_sup = mu_sup + iv.mpf("0.5") / rlo
            mu_p = mu_p + iv.mpf("0.5") * (rlo_inv2t := _1 / (rlo * rlo)) * Dp
            mu_pp = mu_pp + iv.mpf("0.5") * (iv.mpf(4) * Dp * Dp / iv.power(rlo, iv.mpf(4))
                                             + Dpp / iv.power(rlo, iv.mpf(4)))
        Wsq = _sq_iv(iv.mpf(1) + Wp_c)                  # |w|² ≤ (1+a1)² s_ui²
        Wp2 = _sq_iv(Wp_c)
        Wpp2 = (iv.mpf(1) + Wp_c) * Wpp_c
        w_pt = (mu_pp * Wsq + mu_p * iv.mpf(4) * (iv.mpf(1) + Wp_c) * Wp_c * iv.mpf(1)
                + mu_sup * (iv.mpf(2) * Wp2 + iv.mpf(2) * Wpp2))
        for a in range(18):
            for b in range(18):
                Gtil[a][b] = Gtil[a][b] + w_pt * Pis[i][a][b]
    dM2 = iv.mpf("0.5") * op_norm_bound(Gtil)
    info = dict(
        method="integral-form per-edge joint bound（闭式标量权重 × rank-1 PSD 组合）",
        b1=mp.nstr(b1, 8), b2=mp.nstr(b2, 8), a1=mp.nstr(a1, 8), a2=mp.nstr(a2, 8),
        Dp=mp.nstr(mp.mpf(Dp.b), 8),
        max_edge_weight=mp.nstr(max(edge_weights), 8),
        dM2=mp.nstr(mp.mpf(dM2.b), 10),
        note="M(v)−M(0) = DM(0)[v] + ∫(1−t)(d²/dt²)M(tv)dt；一阶项 K-lift、二阶"
             "积分项逐边闭式界（无 box AD）")
    return dM2, info


# ================================================================ R8-3：BD 二阶规则自检（修复回归门）
def bd_rules_selftest():
    """bsqrt/bdiv 二阶传播 vs 精确 mp 有限差分（每次运行强制复核）。

    R7-3 的 .dd 规则含两处 bug（见 BD 类 docstring），使 R7-3 存档的 BD2 box
    通道证书无效。本自检以 r⁻¹、r⁻⁵ 两条解析链逐键对照，任何回归即刻拒绝。"""
    h = mp.mpf("1e-5")
    base = (mp.mpf("1.1"), mp.mpf("-0.7"), mp.mpf("0.5"))
    for p, name in ((mp.mpf(1) / 2, "inv-r"), (mp.mpf(5) / 2, "inv-r5")):
        def build(sv):
            v0 = BD(iv.mpf(sv[0]), {0: _1}, {})
            v1 = BD(iv.mpf(sv[1]), {1: _1}, {})
            x0 = badd(bkonst(base[0]), v0)
            x1 = badd(bkonst(base[1]), v1)
            x2 = bkonst(base[2])
            r2 = badd(badd(bmul(x0, x0), bmul(x1, x1)), bmul(x2, x2))
            r = bsqrt(r2)
            if p == mp.mpf(1) / 2:
                return bdiv(bkonst(_1), r)
            return bdiv(bdiv(bkonst(_1), bmul(r, r2)), r2)

        def fnum(a, b):
            r2 = (base[0] + a) ** 2 + (base[1] + b) ** 2 + base[2] ** 2
            return r2 ** (-p)

        pt = (mp.mpf("0.01"), mp.mpf("-0.02"))
        F = build(pt)
        for (k, l) in ((0, 0), (0, 1), (1, 1)):
            ek = (h if k == 0 else mp.mpf(0), h if k == 1 else mp.mpf(0))
            el = (h if l == 0 else mp.mpf(0), h if l == 1 else mp.mpf(0))
            fd = (fnum(pt[0] + ek[0] + el[0], pt[1] + ek[1] + el[1])
                  - fnum(pt[0] + ek[0] - el[0], pt[1] + ek[1] - el[1])
                  - fnum(pt[0] - ek[0] + el[0], pt[1] - ek[1] + el[1])
                  + fnum(pt[0] - ek[0] - el[0], pt[1] - ek[1] - el[1])) / (4 * h * h)
            ivl = F.dd.get((k, l), _0)
            tol = mp.mpf("1e-9") + mp.mpf("1e-8") * abs(fd)
            require(mp.mpf(ivl.a) - tol <= fd <= mp.mpf(ivl.b) + tol,
                    f"BD second-order rule regression {name}[{k},{l}]: "
                    f"FD {mp.nstr(fd, 10)} vs AD {istr(ivl)}")


# ================================================================ R8-3：D²M 对称双线性提升（联合方向界）
def d2_lift_sigma(delta):
    """σ_max(J₂(box δ)) 的严格区间上界。

    沿线二阶导 F''(t) = Σ_{k,l} v_k v_l·(uᵀ A_{kl}(tv) u)。对固定 u：
    vecsym(T(u)) = J₂ᵀ·vecsym(uuᵀ)，⟨vvᵀ, T(u)⟩ ≤ ‖vvᵀ‖_F·‖T(u)‖_F
    = R²·σ_max(J₂)·‖uuᵀ‖_F（=1）。J₂[(k,l),(a,b)] = √(2−δ_{kl})√(2−δ_{ab})
    ·∂²M_ab/∂v_k∂v_l 的 box δ 区间包络（修复后的 BD2 传播）；K = J₂ᵀJ₂
    171×171 稀疏区间，λ_max(K) ≤ θ+2‖r‖（区间 Ritz＋残差，同 op_norm_bound）。
    方向保留＝K 的 (a,b)-双线性结构不做事后标量解耦——这是对 R7-3 落选的
    标量联合界（方向解耦损失 ~600×）与 box 通道（区间宽度乘性放大）的替代。"""
    M2, _, _, _, _ = build_forms(vfun_box2(delta), iv.mpf(delta * delta), set(S_STAR))
    n = 18
    sq2 = iv.sqrt(iv.mpf(2))
    rows = {}
    for a in range(n):
        for b in range(a, n):
            for (k, l), v in (M2[a][b].dd or {}).items():
                wv = _1 if k == l else sq2
                wab = _1 if a == b else sq2
                rows.setdefault((k, l), {})
                t = v * (wv * wab)
                key = (a, b)
                cur = rows[(k, l)].get(key)
                rows[(k, l)][key] = t if cur is None else \
                    iv.mpf([min(cur.a, t.a), max(cur.b, t.b)])
    cols = [(a, b) for a in range(n) for b in range(a, n)]
    colidx = {c: i for i, c in enumerate(cols)}
    m = len(cols)
    K = [dict() for _ in range(m)]
    n_rows = 0
    for (k, l) in sorted(rows):
        items = sorted(rows[(k, l)].items())
        n_rows += 1
        for i1 in range(len(items)):
            (c1, j1) = items[i1]
            a1 = colidx[c1]
            for c2, j2 in items[i1:]:
                a2 = colidx[c2]
                t = j1 * j2
                if a1 == a2:
                    K[a1][a2] = K[a1].get(a2, _0) + t
                else:
                    K[a1][a2] = K[a1].get(a2, _0) + t
                    K[a2][a1] = K[a2].get(a1, _0) + t
    # float 幂迭代定方向（确定性，不承担证明）
    Kfl = [{c: (mp.mpf(v.a) + mp.mpf(v.b)) / 2 for c, v in row.items()} for row in K]
    x = {0: mp.mpf(1)}
    for _ in range(LIFT_PITER):
        y = {}
        for i_, xi in x.items():
            for c, v in Kfl[i_].items():
                y[c] = y.get(c, mp.mpf(0)) + xi * v
        ny = mp.sqrt(sum((t * t for t in y.values()), mp.mpf(0)))
        if ny == 0:
            break
        x = {c: v / ny for c, v in y.items()}
    xv = {c: iv.mpf(mp.nstr(v, 40)) for c, v in x.items()}
    s2 = sum((_sq_iv(v) for v in xv.values()), _0)
    theta = _0
    for i_, row in enumerate(K):
        xi = xv.get(i_)
        if xi is None:
            continue
        for c, v in row.items():
            xc = xv.get(c)
            if xc is not None:
                theta = theta + xi * v * xc
    r2 = _0
    for i_, row in enumerate(K):
        acc = _0
        any_ = False
        for c, v in row.items():
            xc = xv.get(c)
            if xc is not None:
                acc = acc + v * xc
                any_ = True
        if any_ or i_ in xv:
            res = acc - theta * xv.get(i_, _0)
            r2 = r2 + _sq_iv(res)
    lam_hi = (theta + iv.mpf(2) * iv.sqrt(r2)) / s2 * iv.mpf("1.000000000001")
    sig = iv.sqrt(lam_hi if mp.mpf(lam_hi.a) > 0 else iv.mpf([mp.mpf(0), mp.mpf(lam_hi.b)]))
    info = dict(delta=mp.nstr(mp.mpf(delta), 10),
                nKrows=n_rows, nKcols=m,
                sigma=mp.nstr(mp.mpf(sig.b), 10),
                note="σ_max(J₂)：box δ 上 D²M 的 (v⊗v)×(u⊗u) 对称双线性谱范数")
    return sig, info


def d2_lift_ladder(dmax, steps):
    """共享 δ-阶梯：δ_j = j·dmax/steps（含 δ₀=0），逐档 σ_max 认证。"""
    lad = []
    for j in range(steps + 1):
        delta = dmax * mp.mpf(j) / steps
        sig, info = d2_lift_sigma(delta)
        lad.append((delta, sig, info))
    return lad


def dM2_lift(Rgeo, ladder):
    """dM₂ = R²·∫₀¹(1−t)·σ_max(J₂(box tR))dt——阶梯分段常数（每窗取窗顶 δ 档）。

    窗 [δ_{j−1}/R, δ_j/R]∩[0,1] 用 σ(δ_j)：box(t·R) ⊆ box(δ_j) 对窗内一切 t
    成立 ⟹ 分段常数包络逐窗有效；权重 ∫(1−t)dt 解析。t=1 邻近的大宽度只在
    (1−t) 加权下付费——这是对 R7-3「整箱单值 ½R²·d2op」的结构改进。"""
    R = mp.mpf(Rgeo)
    Riv = iv.mpf(R)
    total = _0
    used = 0
    for j in range(1, len(ladder)):
        delta_j, sig_j = ladder[j][0], ladder[j][1]
        delta_p = ladder[j - 1][0]
        t_hi = delta_j / R
        t_lo = delta_p / R
        if t_hi <= 0:
            continue
        t_hi = t_hi if t_hi < 1 else mp.mpf(1)
        t_lo = t_lo if t_lo < 1 else mp.mpf(1)
        if t_hi <= t_lo:
            continue
        w = iv.mpf(t_hi - t_lo) - iv.mpf((t_hi ** 2 - t_lo ** 2) / 2)
        total = total + w * sig_j
        used += 1
    return Riv * Riv * total, used


def mean_value_widths(R, qmax):
    """box 上中值形式：Δ_cc' = sqrt(Σ_k sup|∂_k|²)·R（Cauchy–Schwarz，ball ⊆ box）。"""
    M, GS, Gh, mu, fv = build_forms(vfun_box(R), qmax, set(S_STAR))
    Dsup = [[_0] * 18 for _ in range(18)]
    DGs = [[_0] * 18 for _ in range(18)]
    DGh = [[_0] * 18 for _ in range(18)]
    Riv = iv.mpf(R)
    for a in range(18):
        for b in range(18):
            s1 = s2 = s3 = _0
            for k in range(27):
                dv = M[a][b].d.get(k)
                if dv is not None:
                    s1 = s1 + _sq_iv(dv)
                dv = GS[a][b].d.get(k)
                if dv is not None:
                    s2 = s2 + _sq_iv(dv)
                dv = Gh[a][b].d.get(k)
                if dv is not None:
                    s3 = s3 + _sq_iv(dv)
            sq = iv.sqrt(s1) * Riv
            Dsup[a][b] = sq
            DGs[a][b] = iv.sqrt(s2) * Riv
            DGh[a][b] = iv.sqrt(s3) * Riv
    return ([[M[a][b].v for b in range(18)] for a in range(18)], Dsup,
            [[GS[a][b].v for b in range(18)] for a in range(18)], DGs,
            [[Gh[a][b].v for b in range(18)] for a in range(18)], DGh, mu, fv)


def fro_norm(D) -> iv.mpf:
    s = _0
    for row in D:
        for x in row:
            s = s + _sq_iv(x)
    return iv.sqrt(s)


def iv_min_hull(X, Y):
    """同一量的两个严格包的「取小」包：lo=min(lo)、hi=min(hi)（纯 iv，端点不做
    mpf 转换——点区间之和在 iv 中可为 1-ulp 宽，mp.mpf 会拒绝）。"""
    lo = X.a if X.a <= Y.a else Y.a
    hi = X.b if X.b <= Y.b else Y.b
    return iv.mpf([lo, hi])


def op_norm_bound(D, iters=40) -> iv.mpf:
    """对称区间矩阵算子范数的区间上界（严格）。

    浮点幂迭代只定方向（同预条件子的角色，不承担证明）；证书＝区间 Ritz＋
    残差界：对称 A、单位 x、θ=xᵀAx、r=Ax−θx ⟹ λ_max(A) ≤ θ + 2‖r‖
    （由 xᵀ(A−θxxᵀ)x=0 ⟹ ‖A−θxxᵀ‖ ≤ 2‖(A−θxxᵀ)x‖=2‖r‖）。区间求值
    （含 x 归一化的外向舍入）＋1e-15 相对垫量。"""
    n = len(D)
    # m̂ = 逐元素上确界的具体非负矩阵（任何实现的逐元素模都被 m̂ 支配）
    mhat = [[max(abs(mp.mpf(D[i][j].a)), abs(mp.mpf(D[i][j].b))) for j in range(n)]
            for i in range(n)]
    mh = [[iv.mpf(mp.nstr(mhat[i][j], 40)) for j in range(n)] for i in range(n)]
    x = [mp.mpf(1)] + [mp.mpf(0)] * (n - 1)
    for _ in range(iters):
        y = [sum((mhat[i][j] * x[j] for j in range(n)), mp.mpf(0)) for i in range(n)]
        ny = mp.sqrt(sum((v * v for v in y), mp.mpf(0)))
        if ny == 0:
            break
        x = [v / ny for v in y]
    xv = [iv.mpf(mp.nstr(v, 40)) for v in x]
    s2 = sum((_sq_iv(v) for v in xv), _0)
    theta = sum((xv[a] * sum((mh[a][b] * xv[b] for b in range(n)), _0)
                 for a in range(n)), _0) / s2
    r2 = _0
    for j in range(n):
        acc = sum((mh[j][a] * xv[a] for a in range(n)), _0) - theta * xv[j]
        r2 = r2 + _sq_iv(acc)
    return (theta + iv.mpf(2) * iv.sqrt(r2)) / s2 * iv.mpf("1.000000000000001")


# ================================================================ N₀（C_R 补基）
def _dot_iv(u, v):
    return sum((u[c] * v[c] for c in range(len(u))), _0)


def _residual(v, basis):
    r = list(v)
    for u in basis:
        p = _dot_iv(u, r)
        for c in range(len(r)):
            r[c] = r[c] - p * u[c]
    return r


def gram_schmidt_completion(CRcols):
    """C_R 3 列 → 正交归一 Ŵ；再带列主元补出 N₀（18×15，区间 GS）。"""
    What = []
    for col in CRcols:
        v = _residual(col, What)
        n2 = _dot_iv(v, v)
        require(mp.mpf(n2.a) > mp.mpf("0.5"),
                f"GS on rotation columns degenerated: {istr(n2)}")
        nrm = iv.sqrt(n2)
        What.append([c / nrm for c in v])
    cands = []
    for c in range(18):
        e = [_0] * 18
        e[c] = _1
        cands.append(_residual(e, What))
    sel = []
    remaining = list(range(18))
    while len(sel) < 15:
        best_i, best_lo, best_r = None, None, None
        for idx in remaining:
            r = _residual(cands[idx], sel)
            lo = mp.mpf(_dot_iv(r, r).a)
            if best_lo is None or lo > best_lo:
                best_i, best_lo, best_r = idx, lo, r
        require(best_lo is not None and best_lo > 0,
                f"pivoted GS exhausted at {len(sel)} (need 15)")
        nrm = iv.sqrt(_dot_iv(best_r, best_r))
        sel.append([c / nrm for c in best_r])
        remaining.remove(best_i)
    return sel, What


# ================================================================ 拉回旋转场漂移（ε_dr）
def rot_pullback_width(Rbox, qmax):
    """sup_{‖v‖≤Rbox} Σ_a ‖m_a(v)−r_a‖² 的区间上界；m_a = dχ_v^*[e_a×ỹ]，
    逐点 m = s₁ z + [s₂+s₁²/cosτ](v·z) v（z=e_a×ỹ 切向，co-transport 公式）。"""
    pts, _rho = PTS_RHO
    totals = _0
    for a in range(3):
        e = [iv.mpf(1) if a == t else _0 for t in range(3)]
        s2tot = _0
        for i in range(9):
            vi = [bkvar(3 * i + t, Rbox) for t in range(3)]
            q = q_of(vi)
            c = series_c(q, qmax)
            s1 = series_s1(q, qmax)
            s2 = series_s2(q, qmax)
            y = [badd(bmul(c, bkonst(pts[i][t])), bmul(s1, vi[t])) for t in range(3)]
            z = [bkonst(e[1] * y[2].v - e[2] * y[1].v),
                 bkonst(e[2] * y[0].v - e[0] * y[2].v),
                 bkonst(e[0] * y[1].v - e[1] * y[0].v)]
            cinv = _1 / c.v
            vz = bdot3(vi, z)
            coeff = badd(s2, bscale(bmul(s1, s1), cinv))
            m = [badd(bmul(s1, z[t]), bmul(bmul(coeff, vz), vi[t])) for t in range(3)]
            ra = [e[1] * pts[i][2] - e[2] * pts[i][1],
                  e[2] * pts[i][0] - e[0] * pts[i][2],
                  e[0] * pts[i][1] - e[1] * pts[i][0]]
            for t in range(3):
                s2tot = s2tot + _sq_iv(m[t].v - ra[t])
        totals = totals + s2tot
    return totals


def rot_gram_lower(r_mp):
    """管上旋转 Gram 下界：9 − λ_max(Σx̄x̄ᵀ) − 6r(1+r)（Gershgorin＋扰动）。"""
    pts, _rho = PTS_RHO
    S = [[_0] * 3 for _ in range(3)]
    for i in range(9):
        for a in range(3):
            for b in range(3):
                S[a][b] = S[a][b] + pts[i][a] * pts[i][b]
    lam_max = max(sum((isup(S[a][b]) for b in range(3)), mp.mpf(0)) for a in range(3))
    r = mp.mpf(r_mp)
    lo = 9 - lam_max - 6 * r * (1 + r)
    require(lo > 1, f"rotation Gram lower bound degenerated: {mp.nstr(lo, 6)}")
    return iv.mpf(lo)


def arcsin2_upper(x_iv) -> iv.mpf:
    """2·arcsin(x) 的区间上界（x ∈ [0, 0.077]；iv.asin 可用则直接，否则级数）。"""
    try:
        return iv.mpf(2) * iv.asin(x_iv)
    except (AttributeError, ValueError):
        pass
    # 级数：arcsin(x) = Σ c_k x^{2k+1}，c_k = C(2k,k)/(4^k(2k+1))；比值 ≤ x²·0.45(k≥1)
    x = x_iv
    s = x
    xk = x
    for k in range(1, 5):
        ck = iv.mpf(mp.mpf(math.comb(2 * k, k)) / (mp.mpf(4) ** k * (2 * k + 1)))
        xk = xk * x * x
        s = s + ck * xk
    return iv.mpf(2) * s * iv.mpf("1.0001")


# ================================================================ 权重化刚性（负对照用）
def build_gs_signed(pts, weights):
    out = [[_0] * 18 for _ in range(18)]
    for (i, j), w in weights.items():
        wiv = iv.mpf(w)
        d = [pts[i][t] - pts[j][t] for t in range(3)]
        row = {}
        for c, (ci, u) in enumerate(BAS):
            if ci == i:
                row[c] = sum((d[t] * u[t] for t in range(3)), _0)
            elif ci == j:
                row[c] = -sum((d[t] * u[t] for t in range(3)), _0)
        for c, Dc in row.items():
            for c2, Dc2 in row.items():
                out[c][c2] = out[c][c2] + wiv * (Dc * Dc2)
    return out


def worst_stress_signflip_residual(pts):
    """S* 应力 ν₂ 权重取负后的最坏切向平衡残差（区间）。"""
    worst = mp.mpf(0)
    for i in range(9):
        acc = [_0, _0, _0]
        for (p, q) in S_STAR:
            d = [pts[p][t] - pts[q][t] for t in range(3)]
            w = 1 if (p, q) in E_NU6 else -1
            sgn = 1 if p == i else (-1 if q == i else 0)
            if sgn:
                for t in range(3):
                    acc[t] = acc[t] + ((d[t] if sgn > 0 else -d[t]) * w)
        for c, (ci, u) in enumerate(BAS):
            if ci == i:
                worst = max(worst, isup(sum((acc[t] * u[t] for t in range(3)), _0)))
    return iv.mpf([-worst, worst])


# ================================================================ advisory 数值（非证明）
def numeric_advisory(zc: float):
    import numpy as np
    rho = math.sqrt(1 - zc * zc)
    s3 = math.sqrt(3.0)
    tri = [(1.0, 0.0), (-0.5, s3 / 2), (-0.5, -s3 / 2)]
    caps = [(0.5, s3 / 2), (-1.0, 0.0), (0.5, -s3 / 2)]
    X = np.array([(rho * c, rho * s, zc) for c, s in tri]
                 + [(rho * c, rho * s, -zc) for c, s in tri]
                 + [(c, s, 0.0) for c, s in caps])
    n = 9

    def bas_of(P):
        B = np.zeros((n, 2, 3))
        for i, p in enumerate(P):
            sxy = math.hypot(p[0], p[1])
            e1 = np.array([-p[1], p[0], 0.0]) / sxy
            B[i, 0] = e1
            B[i, 1] = np.cross(p, e1)
        return B

    def frames(P):
        B = bas_of(P)
        T = np.zeros((27, 18))
        for i in range(n):
            for s in range(2):
                T[3 * i:3 * i + 3, 2 * i + s] = B[i, s]
        W = np.zeros((27, 3))
        for i in range(n):
            x, y, zz = P[i]
            W[3 * i:3 * i + 3, 0] = [0.0, -zz, y]
            W[3 * i:3 * i + 3, 1] = [zz, 0.0, -x]
            W[3 * i:3 * i + 3, 2] = [-y, x, 0.0]
        return T, W

    def hess_lam(P):
        T, W = frames(P)
        H = np.zeros((27, 27))
        lam = np.zeros(n)
        for i in range(n):
            g = np.zeros(3)
            for j in range(n):
                if i == j:
                    continue
                d = P[i] - P[j]
                g -= d / np.linalg.norm(d) ** 3
            lam[i] = g @ P[i]
        for i in range(n):
            for j in range(i + 1, n):
                d = P[i] - P[j]
                r = np.linalg.norm(d)
                Mm = 3.0 * r ** -5.0 * np.outer(d, d) - r ** -3.0 * np.eye(3)
                H[3*i:3*i+3, 3*i:3*i+3] += Mm
                H[3*j:3*j+3, 3*j:3*j+3] += Mm
                H[3*i:3*i+3, 3*j:3*j+3] -= Mm
                H[3*j:3*j+3, 3*i:3*i+3] -= Mm
        for i in range(n):
            H[3*i:3*i+3, 3*i:3*i+3] -= lam[i] * np.eye(3)
        CRn = T.T @ W
        U, _, _ = np.linalg.svd(CRn, full_matrices=True)
        Z = U[:, 3:]
        return float(np.linalg.eigvalsh(Z.T @ (T.T @ H @ T) @ Z)[0])

    lq = hess_lam(X)
    T0, W0 = frames(X)
    CRn = T0.T @ W0
    U, _, _ = np.linalg.svd(CRn, full_matrices=True)
    Z0 = U[:, 3:]
    B0 = bas_of(X)

    def rig(edges):
        Rm = np.zeros((len(edges), 18))
        for e, (i, j) in enumerate(edges):
            d = X[i] - X[j]
            for s in range(2):
                Rm[e, 2 * i + s] = d @ B0[i, s]
                Rm[e, 2 * j + s] = -d @ B0[j, s]
        return Rm

    def eigq(Rm):
        rank = int(np.linalg.matrix_rank(Rm, tol=1e-9))
        Gq = Rm.T @ Rm
        return rank, float(np.linalg.eigvalsh(Z0.T @ Gq @ Z0)[0]), 18 - rank

    r12 = rig(E_NU6)
    U2, S2, Vt2 = np.linalg.svd(r12, full_matrices=True)
    rotfrac = []
    for krow in Vt2[int(np.linalg.matrix_rank(r12, tol=1e-9)):]:
        cc = np.linalg.lstsq(CRn, krow, rcond=None)[0]
        rotfrac.append(float(np.linalg.norm(CRn @ cc) / np.linalg.norm(krow)))
    rank12, lam12, ker12 = eigq(r12)
    rankS, lamS, kerS = eigq(rig(S_STAR))
    rankA, lamA, kerA = eigq(rig(E_NU6 + E_NU1 + E_NU2))
    rank36, lam36, ker36 = eigq(rig(PAIRS))

    rng = np.random.default_rng(SEED)
    samples = {}
    for rr in (0.005, 0.02, 0.076):
        vals = []
        for _ in range(12):
            a = rng.normal(size=18)
            a /= np.linalg.norm(a)
            vv = np.zeros((n, 3))
            for c in range(18):
                vv[c // 2] += a[c] * B0[c // 2, c % 2]
            vv *= rr / max(np.linalg.norm(vv), 1e-300)
            Y = np.zeros((n, 3))
            for i in range(n):
                tau = np.linalg.norm(vv[i])
                Y[i] = X[i] if tau < 1e-14 else math.cos(tau) * X[i] + math.sin(tau) / tau * vv[i]
            vals.append(hess_lam(Y))
        samples[f2s(rr)] = {"min": f2s(min(vals)), "mean": f2s(sum(vals) / len(vals))}
    return {
        "note": "float64 advisory（非证明）；区间证书独立于本块",
        "lambda0Numeric": f2s(lq),
        "rigidity": {
            "nu6_12": {"rank": rank12, "kernelDim": ker12,
                       "maxRotationFractionInKernel": f2s(max(rotfrac)),
                       "lambdaOnQuotient": f2s(lam12)},
            "nu6_nu2_18": {"rank": rankS, "kernelDim": kerS, "lambdaOnQuotient": f2s(lamS)},
            "nu6_nu1_nu2_24": {"rank": rankA, "kernelDim": kerA, "lambdaOnQuotient": f2s(lamA)},
            "all36": {"rank": rank36, "kernelDim": ker36, "lambdaOnQuotient": f2s(lam36)},
        },
        "trueQuotientLambdaSamples": samples,
    }


# ================================================================ 主流程
def run_certificate():
    global PTS_RHO, BAS
    # ---------- 0a) R8-3：BD 二阶规则自检（R7-3 规则 bug 的修复回归门）
    bd_rules_selftest()
    # ---------- 0) z* 自隔离（宽度 1e-10）＋断言 ⊆ R1 存档区间
    r1_path = HERE / "results" / "local_min.json"
    require(r1_path.exists(), "missing results/local_min.json (run local_min.py first)")
    r1 = json.load(open(r1_path))
    lo_s, hi_s = [s.strip() for s in r1["zStarInterval"].strip("[]").split(",")]
    lo, hi = lm.isolate(*lm.BRACKET, mp.mpf(Z_ISO_WIDTH))[:2]
    require(mp.mpf(lo.a) >= mp.mpf(lo_s) and mp.mpf(hi.b) <= mp.mpf(hi_s),
            f"self-isolation [{mp.nstr(lo.a, 10)}, {mp.nstr(hi.b, 10)}] not inside R1 archive")
    Ep_lo, Ep_hi = lm.E_dual(lo).d1, lm.E_dual(hi).d1
    require(lm.strictly_negative(Ep_lo) and lm.strictly_positive(Ep_hi),
            "E' sign change failed on the isolation interval")
    zc_mp = (mp.mpf(lo.a) + mp.mpf(hi.b)) / 2
    ZC = iv.mpf(mp.nstr(zc_mp, 45))
    Epp = lm.E_dual(iv.mpf(mpmath.mpi(mp.mpf(lo.a), mp.mpf(hi.b)))).d2
    require(lm.strictly_positive(Epp), "E'' must stay > 0 on isolation interval")

    # ---------- 1) 参考构型 X̄、固定基、Ē
    pts, rho = ttp_points(ZC)
    PTS_RHO = (pts, rho)
    BAS = tangent_basis_iv(pts)
    for c, (i, u) in enumerate(BAS):
        n2 = sum((u[t] * u[t] for t in range(3)), _0)
        require(isup(n2 - _1) < mp.mpf("1e-30"), f"basis col {c} not unit: {istr(n2)}")
        for c2 in range(c + 1, len(BAS)):
            i2, u2 = BAS[c2]
            if i == i2:
                dd = sum((u[t] * u2[t] for t in range(3)), _0)
                require(isup(dd) < mp.mpf("1e-30"), f"basis cols {c},{c2} not orthogonal")
    Ebar = _0
    for (i, j) in PAIRS:
        d = [pts[i][t] - pts[j][t] for t in range(3)]
        r2 = sum((d[t] * d[t] for t in range(3)), _0)
        Ebar = Ebar + _1 / iv.sqrt(r2)
    e_star_entry = lm.load_e_star()
    e_star = mp.mpf(str(e_star_entry["highPrecision"]))
    dE = max(abs(mp.mpf(Ebar.a) - e_star), abs(mp.mpf(Ebar.b) - e_star))
    require(dE <= mp.mpf("1e-8"), f"E(Xbar) {istr(Ebar)} vs E* {mp.nstr(e_star, 12)}: {mp.nstr(dE, 4)}")

    # ---------- 2) 点值形式 + N₀ + λ₀/λ_S0/σ + 自应力 + γ
    M0B, GS0B, Gh0B, mu0, fv0 = build_forms(vfun_point, iv.mpf(0), set(S_STAR))
    M0 = [[x.v for x in row] for row in M0B]
    GS0 = [[x.v for x in row] for row in GS0B]
    Gh0 = [[x.v for x in row] for row in Gh0B]
    g_err = max(isup(Gh0[a][b] - (_1 if a == b else _0))
                for a in range(18) for b in range(18))
    require(g_err < mp.mpf("1e-12"), f"Ghat(0) != I: {mp.nstr(g_err, 4)}")
    CR = [[None] * 3 for _ in range(18)]
    for c, (i, u) in enumerate(BAS):
        x, y, zz = pts[i][0], pts[i][1], pts[i][2]
        CR[c][0] = -zz * u[1] + y * u[2]
        CR[c][1] = zz * u[0] - x * u[2]
        CR[c][2] = -y * u[0] + x * u[1]
    CRcols = [[CR[c][a] for c in range(18)] for a in range(3)]
    N0, What = gram_schmidt_completion(CRcols)

    def restrict(A):
        return [[sum((N0[a][c] * A[c][c2] * N0[b][c2]
                      for c in range(18) for c2 in range(18)), _0)
                 for b in range(15)] for a in range(15)]

    lambda0 = certify_lambda(restrict(M0), LAMBDA0_LADDER, "M(0) on N0")
    lambdaS0 = certify_lambda(restrict(GS0), LAMBDA_S_LADDER, "GS(0) on N0")
    sigma = _0
    for a in range(3):
        s2 = _0
        for r_ in range(18):
            acc = sum((What[a][c] * M0[r_][c] for c in range(18)), _0)
            s2 = s2 + _sq_iv(acc)
        sigma = max(sigma, iv.sqrt(s2))
    # 旋转在刚性矩阵核中：精确恒等式 d·(ω×d)=0（区间复核）
    for (i, j) in PAIRS:
        d = [pts[i][t] - pts[j][t] for t in range(3)]
        w1 = [pts[i][1] * d[2] - pts[i][2] * d[1],
              pts[i][2] * d[0] - pts[i][0] * d[2],
              pts[i][0] * d[1] - pts[i][1] * d[0]]
        res = sum((d[t] * w1[t] for t in range(3)), _0)
        require(isup(res) < mp.mpf("1e-30"), "rotation-in-kernel identity failed")
    # S* 全 1 权重正自应力：每顶点 Σ±d_e ∥ x_i（精确法向平衡）
    stress_res = mp.mpf(0)
    for i in range(9):
        acc = [_0, _0, _0]
        for (p, q) in S_STAR:
            d = [pts[p][t] - pts[q][t] for t in range(3)]
            sgn = 1 if p == i else (-1 if q == i else 0)
            if sgn:
                for t in range(3):
                    acc[t] = acc[t] + (d[t] if sgn > 0 else -d[t])
        for c, (ci, u) in enumerate(BAS):
            if ci == i:
                stress_res = max(stress_res, isup(sum((acc[t] * u[t] for t in range(3)), _0)))
    require(stress_res < mp.mpf("1e-30"),
            f"S* unit self-stress residual too large: {mp.nstr(stress_res, 4)}")
    # 全图解析正自应力 ω_e = f_e^{-3/2}（临界性恒等式区间复核）
    full_res = mp.mpf(0)
    for i in range(9):
        acc = [_0, _0, _0]
        for (p, q) in PAIRS:
            d = [pts[p][t] - pts[q][t] for t in range(3)]
            r = iv.sqrt(sum((d[t] * d[t] for t in range(3)), _0))
            wgt = _1 / (r * r * r)
            sgn = 1 if p == i else (-1 if q == i else 0)
            if sgn:
                for t in range(3):
                    acc[t] = acc[t] + (d[t] if sgn > 0 else -d[t]) * wgt
        for c, (ci, u) in enumerate(BAS):
            if ci == i:
                full_res = max(full_res, isup(sum((acc[t] * u[t] for t in range(3)), _0)))
    require(full_res < mp.mpf("1e-8"),
            f"full-graph f^-3/2 stress residual too large: {mp.nstr(full_res, 4)}")
    # 临界性残差 γ = ‖切向∇E(X̄)‖（∝|E'|，z 隔离 1e-10 ⟹ 微小）
    g_red = []
    for c, (i, u) in enumerate(BAS):
        acc = _0
        for j in range(9):
            if j == i:
                continue
            d = [pts[i][t] - pts[j][t] for t in range(3)]
            r = iv.sqrt(sum((d[t] * d[t] for t in range(3)), _0))
            for t in range(3):
                acc = acc - (d[t] * u[t]) / (r * r * r)
        g_red.append(acc)
    gamma = iv.sqrt(sum((_sq_iv(g) for g in g_red), _0)) * iv.mpf("1.002")
    # 1.002 = 2·arcsin(R_MAX/2)/R_MAX 的上界（测地长/弦长因子；h'(0) 以测地范数 T≥d 进入）

    # ---------- 3) 目标半径公式值（对账）＋分箱
    r_formula = iv.sqrt(iv.mpf(2) * iv.mpf(DELTA_E_CAP) / iv.mpf(LAMBDA_REF_FLM))
    require(abs(mp.mpf(r_formula.a) - mp.mpf(R_TARGET_FORMULA)) < mp.mpf(R_TOL)
            and abs(mp.mpf(r_formula.b) - mp.mpf(R_TARGET_FORMULA)) < mp.mpf(R_TOL),
            f"r_formula {istr(r_formula)} != {R_TARGET_FORMULA}")
    R_MAX = 2 * mp.mpf(R_TARGET_FORMULA)
    bins = [R_MAX * mp.mpf(2) ** ((k - K_BINS) / 4) for k in range(1, K_BINS + 1)]

    # ---------- 3b) R7-3：dM 的 Taylor 分解（sharp DM(0) K-lift + 二阶联合界）
    M0dB, GS0dB, Gh0dB, mu0dB, fv0dB = build_forms(
        vfun_point_deriv, iv.mpf(0), set(S_STAR))
    M0_f = [[(mp.mpf(M0[a][b].a) + mp.mpf(M0[a][b].b)) / 2 for b in range(18)]
            for a in range(18)]
    klam, klam_info = klift_cert(M0dB)
    K_TAYLOR_MAX_BIN = K_LIFT_MAX_BIN   # R8-3：提升通道接管 ≤34 箱；33 为 R7-3 历史口径
    R2BOX = mp.mpf(arcsin2_upper(iv.mpf(bins[33]) / 2).b)
    d2op, d2_legacy_info = taylor_d2_pass(R2BOX)   # 修复规则后复算（legacy 对照）
    # R8-3：σ-阶梯（共享 δ-阶梯 + 区间 Ritz 逐档 σ_max 认证）
    DLIFT = mp.mpf(arcsin2_upper(iv.mpf(bins[K_LIFT_MAX_BIN]) / 2).b)
    lift_ladder = d2_lift_ladder(DLIFT, LIFT_J)
    lift_ladder_info = [info for _, _, info in lift_ladder]
    # A_k(0) float 中点（advisory 线性部分复算用）
    Akeys = sorted({k for a in range(18) for b in range(a, 18) for k in M0dB[a][b].d})
    A0f = {k: [[(mp.mpf(M0dB[a][b].d.get(k, _0).a) + mp.mpf(M0dB[a][b].d.get(k, _0).b)) / 2
                if a <= b else (mp.mpf(M0dB[b][a].d.get(k, _0).a) + mp.mpf(M0dB[b][a].d.get(k, _0).b)) / 2
                for b in range(18)] for a in range(18)] for k in Akeys}

    def dM_taylor(Rbox, kbin):
        """M(v)−M(0) 于 ‖v‖≤Rbox：一阶 K-lift ＋ 二阶项（R8-3 提升通道，kbin ≤ 阈值）。"""
        first = iv.mpf(Rbox) * klam
        if kbin <= K_LIFT_MAX_BIN:
            second, _w = dM2_lift(Rbox, lift_ladder)
        else:
            second = None
        return (first if second is None else first + second), first, second

    # advisory 交叉核对：定点采样 |u^T(M(v)−M(0)−DM(0)[v])u| ≤ 二阶界（float，非证明；
    # 同时对照联合界（更松、但无半径上限）与 BD2 box 通道）
    adv_taylor = []
    rng_t = random.Random(SEED)
    for kbin_chk in (20, 28, 32, 33):
        r_chk = bins[kbin_chk]
        Rb_chk = mp.mpf(arcsin2_upper(iv.mpf(r_chk) / 2).b)
        _tot, _f, second = dM_taylor(Rb_chk, kbin_chk)
        joint2, _ji = joint_second_order(Rb_chk)
        Mv_samples = []
        vfls = []
        for _ in range(8):
            vfl = [rng_t.uniform(-1, 1) for _ in range(27)]
            nrm = mp.sqrt(sum((x * x for x in vfl), mp.mpf(0)))
            vfl = [x * float(Rb_chk) / float(nrm) for x in vfl]
            vfls.append(vfl)
            MvB, _, _, _, _ = build_forms(vfun_fixed(vfl), iv.mpf(0), set(S_STAR))
            Mv_samples.append([[(mp.mpf(MvB[a][b].v.a) + mp.mpf(MvB[a][b].v.b)) / 2
                                for b in range(18)] for a in range(18)])
        worst = 0.0
        for _ in range(60):
            u = [rng_t.uniform(-1, 1) for _ in range(18)]
            nu = math.sqrt(sum(x * x for x in u))
            u = [x / nu for x in u]
            for vfl, Mv in zip(vfls, Mv_samples):
                lin = 0.0
                for k in Akeys:
                    Ak = A0f[k]
                    lin += vfl[k] * sum((u[a] * sum((Ak[a][b] * u[b] for b in range(18)), 0.0)
                                         for a in range(18)), 0.0)
                val = (sum((u[a] * sum((Mv[a][b] * u[b] for b in range(18)), mp.mpf(0))
                            for a in range(18)), mp.mpf(0))
                       - sum((u[a] * sum((M0_f[a][b] * u[b] for b in range(18)), mp.mpf(0))
                              for a in range(18)), mp.mpf(0)))
                worst = max(worst, abs(float(val) - float(lin)))
        ok = worst <= float(mp.mpf(second.b)) * (1 + 1e-9)
        ok_joint = worst <= float(mp.mpf(joint2.b)) * (1 + 1e-9)
        adv_taylor.append(dict(
            bin=kbin_chk, r=mp.nstr(mp.mpf(r_chk), 8),
            dM2_bd2box_hi=mp.nstr(mp.mpf(second.b), 10),
            dM2_joint_hi=mp.nstr(mp.mpf(joint2.b), 10),
            sampled_rem_sup=worst, holds=ok, joint_holds=ok_joint))
        require(ok and ok_joint,
                f"second-order advisory check FAILED at bin {kbin_chk}: "
                f"sampled {worst} > cert bd2 {mp.nstr(mp.mpf(second.b), 8)} / "
                f"joint {mp.nstr(mp.mpf(joint2.b), 8)}")

    # 代表箱（bins[32] = 0.0095）处联合界信息（对照保留；实际用 BD2 box 通道）
    Rb32 = mp.mpf(arcsin2_upper(iv.mpf(bins[32]) / 2).b)
    _j2, joint_info_r = joint_second_order(Rb32)

    bin_out = []
    bin_store = []      # (kbin, Rbox, dM_leg, dM_first)——负对照 e（通道换回）复算用
    for kbin, rbin in enumerate(bins):
        r_mp = mp.mpf(rbin)
        rho_geo = arcsin2_upper(iv.mpf(r_mp) / 2)
        Rbox = mp.mpf(rho_geo.b)
        qmax = iv.mpf(Rbox * Rbox)
        (Mbx, DM, GSbx, DGS, Ghbx, DGH, mub, fvb) = mean_value_widths(Rbox, qmax)
        dM_leg = op_norm_bound(DM)
        dM_first = dM_second = None
        if kbin <= K_LIFT_MAX_BIN:
            dM_first = iv.mpf(Rbox) * klam
            dM_second, _w = dM2_lift(Rbox, lift_ladder)
            dM = iv_min_hull(dM_leg, dM_first + dM_second)
        else:
            dM = dM_leg
        dGS = op_norm_bound(DGS)
        dGh = fro_norm(DGH)
        mres = rot_pullback_width(Rbox, qmax)
        lam_rg_lo = rot_gram_lower(r_mp)
        eps_dr2 = iv.mpf(3) * mres / lam_rg_lo
        eps_dr = iv.sqrt(eps_dr2 if mp.mpf(eps_dr2.a) > 0 else iv.mpf([mp.mpf(0), mp.mpf(eps_dr2.b)]))
        rt2 = iv.sqrt(iv.mpf(2)) * iv.mpf(r_mp)
        f_lo, f_hi = {}, {}
        for (i, j) in PAIRS:
            ell = iv.sqrt(fv0[(i, j)])
            lo_ = ell - rt2
            require(mp.mpf(lo_.a) > 0,
                    f"edge ({i},{j}) chord crosses 0 at r={mp.nstr(r_mp, 5)}")
            f_lo[(i, j)] = lo_ * lo_
            f_hi[(i, j)] = (ell + rt2) * (ell + rt2)
        f_all_min = min(f_lo.values(), key=lambda I: mp.mpf(I.a))
        f_all_max = max(f_hi.values(), key=lambda I: mp.mpf(I.b))
        f_S_min = min((f_lo[e] for e in S_STAR), key=lambda I: mp.mpf(I.a))
        sum_f_m3h2 = _0
        for e in PAIRS:
            sum_f_m3h2 = sum_f_m3h2 + _1 / iv.sqrt(f_lo[e] * f_lo[e] * f_lo[e])
        c_curv = min((iv.mpf("0.5") * sum((_1 / iv.sqrt(f_lo[(min(i, j), max(i, j))])
                                           for j in range(9) if j != i), _0)
                      for i in range(9)), key=lambda I: mp.mpf(I.a))
        lamS_r = (lambdaS0 * (_1 - eps_dr2) - dGS) / (_1 + dGh)
        lam_task = iv.mpf(4) * lamS_r
        mu_klt = (iv.mpf(3) / 4) / iv.sqrt(f_all_min * f_all_min * iv.sqrt(f_all_min)) * lam_task \
            - iv.mpf(2) * sum_f_m3h2 + c_curv
        mu_t = (lambda0 * (_1 - eps_dr2) - iv.mpf(2) * sigma * eps_dr - dM) / (_1 + dGh)
        L0sup = (qmax / iv.mpf(6)) * (iv.mpf(3) * iv.mpf(rho_geo.b))
        omega_sup = L0sup / lam_rg_lo
        Gg2 = _0
        for i in range(9):
            s_ = _0
            for j in range(9):
                if j == i:
                    continue
                s_ = s_ + _1 / f_lo[(min(i, j), max(i, j))]
            Gg2 = Gg2 + _sq_iv(s_)
        Ggrad = iv.sqrt(Gg2)
        cross = iv.mpf(2) * omega_sup * Ggrad + iv.mpf(6) * omega_sup * omega_sup * Ggrad
        mu_eff = mu_t - cross
        bin_store.append((kbin, Rbox, dM_leg, dM_first, eps_dr2, eps_dr, dGh, cross))
        bin_out.append({
            "r": mp.nstr(r_mp, 8),
            "vBoxRadius": mp.nstr(Rbox, 10),
            "fMinInterval": istr(f_all_min),
            "fMaxInterval": istr(f_all_max),
            "fSMinInterval": istr(f_S_min),
            "M_D2fPerEdge": "4 (|D2 f_e[v,v]| = 2|dv_e|^2 <= 4||v||^2)",
            "sumFinv32": istr(sum_f_m3h2),
            "lambdaS": istr(lamS_r),
            "lambdaTask": istr(lam_task),
            "deltaMFro": istr(dM),
            "deltaMFroLegacy": istr(dM_leg),
            "deltaMFroTaylor1st": (None if dM_first is None else istr(dM_first)),
            "deltaMFroTaylor2nd": (None if dM_second is None else istr(dM_second)),
            "taylorDecompositionApplied": dM_first is not None,
            "deltaG": istr(dGh),
            "epsDrift": istr(eps_dr),
            "crossTerm": istr(cross),
            "muTransport": istr(mu_t),
            "mu": istr(mu_eff),
            "muKltSplit": istr(mu_klt),
            "cCurv": istr(c_curv),
            "gradNormTube": istr(Ggrad),
        })
        print(f"  bin r={mp.nstr(r_mp, 6)}: dM={mp.nstr(mp.mpf(dM.a), 4)} "
              f"mu={istr(mu_eff)} muKLT={istr(mu_klt)}", flush=True)

    # prefix 半径：保证 [前缀全部 μ>0] 的最大分箱
    def mu_ends(b):
        s = b["mu"].strip("[]").split(",")
        return mp.mpf(s[0]), mp.mpf(s[1])

    r_star_idx = -1
    for k in range(len(bin_out)):
        if all(mu_ends(bin_out[j])[0] > 0 for j in range(k + 1)):
            r_star_idx = k
    require(r_star_idx >= 0, "no bin with certified mu > 0")
    r_star = bins[r_star_idx]
    s_ = bin_out[r_star_idx]["mu"].strip("[]").split(",")
    mu_star = iv.mpf([mp.mpf(s_[0]), mp.mpf(s_[1])])
    require(mp.mpf(mu_star.a) > 0, "internal consistency: r* requires mu(r*) > 0")

    # ---------- 4) 二次增长定理常数
    vz_norm = iv.sqrt(iv.mpf(6)) / rho
    dz = max(mp.mpf(zc_mp) - mp.mpf(lo_s), mp.mpf(hi_s) - mp.mpf(zc_mp))
    delta_orb = vz_norm * iv.mpf(dz)
    d_excl = iv.mpf(2) * gamma / mu_star

    # ---------- 5) 负对照（三件，全部必须按预期触发）
    controls = {}
    mu_top_lo, mu_top_hi = mu_ends(bin_out[-1])
    require(mu_top_hi <= 0,
            f"double-radius control FAILED: mu(2x0.07601) upper end {mp.nstr(mu_top_hi, 6)} > 0")
    nxt = bin_out[r_star_idx + 1] if r_star_idx + 1 < len(bin_out) else None
    require(nxt is None or mu_ends(nxt)[1] <= 0, "adjacent-bin control FAILED")
    controls["doubleRadiusControl"] = {
        "radiusDoubled": mp.nstr(R_MAX, 10),
        "muUpper": mp.nstr(mu_top_hi, 8),
        "triggered": True,
        "note": "负对照 a：μ(2×r_target) 区间上端 ≤ 0——加倍半径处证书拒绝",
        **({"adjacentBinMuUpper": mp.nstr(mu_ends(nxt)[1], 8)} if nxt else {}),
    }
    GS_bad = build_gs_signed(pts, {e: (1 if e in E_NU6 else -1) for e in S_STAR})
    try:
        certify_pd_preconditioned(restrict(GS_bad), "tampered GS (1,-1) weights")
        raise CheckError("stress-weight control FAILED: (1,-1)-weighted Gram unexpectedly PD")
    except CheckError as e:
        require(("positive definite" in str(e)) or ("not PD" in str(e)),
                f"stress-weight control wrong reason: {e}")
        controls["stressWeightControl"] = {
            "tampering": "S* Gram 权重 (nu6:+1, nu2:-1)（自应力权重改非正）",
            "triggered": True, "message": str(e)[:160],
        }
    acc_bad = worst_stress_signflip_residual(pts)
    require(not contains_zero(acc_bad) or isup(acc_bad) > mp.mpf("1e-2"),
            "stress-signflip control FAILED: flipped stress still equilibrated")
    controls["stressSignFlipControl"] = {
        "tampering": "S* 应力 ν₂ 边权重取负",
        "tangentialResidual": istr(acc_bad),
        "triggered": True,
    }
    mu_bad = -mu_star
    try:
        require(mp.mpf(mu_bad.a) > 0, "growth claim requires mu > 0 (rejected sign-flipped mu)")
        raise CheckError("mu-signflip control FAILED: -mu accepted")
    except CheckError as e:
        require("requires mu > 0" in str(e), f"mu-signflip control wrong reason: {e}")
        controls["muSignFlipControl"] = {"tampering": "mu -> -mu", "triggered": True,
                                         "message": str(e)[:120]}
    # 负对照 e（R8-3 联合通道专属）：把二阶项换回标量方向解耦联合界
    # （joint_second_order，R7-3 落选通道）⇒ r* 必须回退至旧档及以下——
    # 证明本证书的提升通道（方向保留的 σ_max(J₂) 窗口积分）被实际使用。
    fb_mu_ok = []
    fb_dM2_at = {}
    for (kbin, Rbox, dM_leg_s, dM_first_s, edr2, edr, dgh, crs) in bin_store:
        if kbin > K_LIFT_MAX_BIN:
            dM_fb = dM_leg_s
        else:
            j2, _ji = joint_second_order(Rbox)
            fb_dM2_at[kbin] = mp.mpf(j2.b)
            dM_fb = iv_min_hull(dM_leg_s, dM_first_s + j2)
        mu_fb = (lambda0 * (_1 - edr2) - iv.mpf(2) * sigma * edr - dM_fb) / (_1 + dgh) - crs
        fb_mu_ok.append(mp.mpf(mu_fb.a) > 0)
    fb_idx = -1
    for k in range(len(fb_mu_ok)):
        if all(fb_mu_ok[:k + 1]):
            fb_idx = k
    require(fb_idx >= 0, "fallback control: scalar-decoupled channel produced no positive bin")
    r_fb = bins[fb_idx]
    require(mp.mpf(r_fb) <= mp.mpf(R73_ARCHIVE["r_star"]) and mp.mpf(r_fb) < r_star,
            f"fallback control FAILED: scalar channel r*={mp.nstr(r_fb, 9)} "
            f"not <= archived {R73_ARCHIVE['r_star']} / < new r*")
    controls["channelSwapScalarDecoupledControl"] = {
        "tampering": "二阶通道 σ_max(J₂) 窗口积分 → 标量方向解耦联合界（joint_second_order）",
        "fallbackRstar": mp.nstr(r_fb, 10),
        "archivedR73Rstar": R73_ARCHIVE["r_star"],
        "newRstar": mp.nstr(r_star, 10),
        "triggered": True,
        "note": "换回标量解耦 ⇒ r* 回退旧档及以下（提升通道的方向保留结构不可替代）",
    }
    # 内部一致性（门 ②）：μ>0 ⟺ r*>0
    require((mp.mpf(mu_star.a) > 0) == (r_star_idx >= 0),
            "internal consistency mu>0 <=> r*>0 violated")

    # ---------- 6) advisory + 对账 + 装配
    adv = numeric_advisory(float(zc_mp))
    tube_path = RESULTS / "tube.json"
    ballscan = {}
    if tube_path.exists():
        ballscan = json.load(open(tube_path)).get("ball_scan", {}).get("r=0.076", {})
    lam0_str = mp.nstr(mp.mpf(lambda0.a), 10)
    mu_klt_all_neg = all(istr_parse_hi(b["muKltSplit"]) <= 0 for b in bin_out)
    result = {
        "schema": "thomson-n9/bounds/l6-intube/2",
        "claim": (
            f"记 X̄=X(z_c)（z_c={mp.nstr(zc_mp, 16)}，自隔离 z* 宽度 {Z_ISO_WIDTH}，⊆ R1 存档）、"
            f"Ē=E(X̄)（区间 {istr(Ebar)}）。认证常数 μ={istr(mu_star)}（分箱半径 "
            f"r*={mp.nstr(r_star, 8)}）与 γ={istr(gamma)}：对一切 Y∈(S²)⁹、弦距 "
            f"d(Y):=min_Q‖Y−QX̄‖_R²⁷ ≤ r*：E(Y) ≥ Ē − γ·d(Y) + (μ/2)·d(Y)²（模 SO(3)）。"
            f"竞争者：E(Y) ≤ Ē ⟹ d(Y) ≤ 2γ/μ={istr(d_excl)}（r* 球内）。与 R1 存档 TTP 轨道的 "
            f"Hausdorff ≤ {istr(delta_orb)}。证明＝KLT §7.4 二阶分解（免 D³E）＋固定坐标输运 "
            "Hessian 中值形式区间界＋Procrustes 最优旋转匹配测地线积分（角动量 O(r³)＋交叉项入账）。"
            "R8-3：二阶余项改用 D²M 的 (v⊗v)×(u⊗u) 对称双线性提升 σ_max(J₂) 于 δ-阶梯的 "
            "(1−t) 加权窗口积分（方向耦合保留；BD 传播规则经修复并以解析自检逐次复核）"),
        "manifold": "(S^2)^9 ⊂ R^27；18 维固定正交切基系数空间；SO(3) 轨道 3 维；商空间 N0 15 维",
        "zCenter": {"value": mp.nstr(zc_mp, 20), "selfIsolationWidth": Z_ISO_WIDTH,
                    "insideR1Archive": [lo_s, hi_s], "EprimeSignChange": True,
                    "EppOnIsolation": lm.istr(Epp)},
        "Ebar": {"interval": istr(Ebar),
                 "eStarHighPrecision": str(e_star_entry["highPrecision"]),
                 "absDiffUpper": mp.nstr(dE, 6)},
        "lambda0": {"certified": lam0_str, "numeric": adv["lambda0Numeric"],
                    "sigmaRotationResidue": istr(sigma),
                    "fullLocalMinCrosscheck": {"file": "results/full_local_min.json",
                                               "value": LAMBDA_REF_FLM,
                                               "compatible": mp.mpf(lambda0.a) >= mp.mpf(LAMBDA_REF_FLM) - mp.mpf("1e-6")}},
        "rigidity": {
            "edgeSetPrimary": {
                "id": "nu6（内积 0.3553；tube.json /ttp_spectrum 重数 12）",
                "size": 12, "infinitesimallyRigid": False,
                "reason": "Maxwell 计数：球面 9 顶点无穷小刚性需 ≥2·9−3=15 条边；12 条边 "
                          "⟹ rank ≤ 12 < 15——任何构型处结构性不可能（纯数学）。数值：rank 12、"
                          "核 6 维 = 3 旋转 + 3 挠曲",
                "numeric": adv["rigidity"]["nu6_12"]},
            "edgeSetCertified": {
                "id": "S* = nu6 ∪ nu2（12 短边 + 6 帽对顶边，18 条）",
                "size": 18, "lambdaS0": mp.nstr(mp.mpf(lambdaS0.a), 10),
                "kernelExactlyRotations": True,
                "proof": "旋转场在刚性矩阵核中＝精确恒等式 d·(ω×d)=0（区间复核 1e-30）；"
                         "N₀ 上 λ_S0>0 区间 Cholesky 排除非旋转核 ⟹ 核恰为 SO(3) 3 维",
                "positiveSelfStress": {
                    "weights": "全 1（18 条边严格正）",
                    "structure": "每顶点 Σ_{e∋i} ±d_e = 3x_T（三角顶）/ 6x_C（帽顶）——"
                                 "精确法向平衡（Σcaps=Σtop+bottom=0 的 D3h 后果）",
                    "tangentialResidualMaxAbs": mp.nstr(stress_res, 6),
                    "strictlyPositive": True},
                "numeric": adv["rigidity"]["nu6_nu2_18"]},
            "fullGraphAnalyticStress": {
                "weights": "omega_e = f_e^{-3/2}（恰为 D²E 分解的负项系数）",
                "identity": "临界性 ∇_iE=μ_i y_i ⟺ Σ_j (y_i−y_j)/r_ij³ = μ_i y_i ⟹ 正自应力",
                "tangentialResidualMaxAbs": mp.nstr(full_res, 6)},
            "alternatesNumeric": {"nu6_nu1_nu2_24": adv["rigidity"]["nu6_nu1_nu2_24"],
                                  "all36": adv["rigidity"]["all36"]},
            "kltLemma71Note": "KLT 引理 7.1 TTP 版：接触图（ν₆ 12 边）单独不刚"
                              "（KLT N=8 有 16≥2·8−3 条接触边；N=9 TTP 只有 12<15）；"
                              "增广 ν₂ 后刚性＋严格正自应力成立（本块区间证书）"},
        "bins": bin_out,
        "binning": {"law": f"r_k = R_MAX·2^((k−{K_BINS})/4), k=1..{K_BINS}（四分之一倍频程）",
                    "R_MAX": mp.nstr(R_MAX, 10),
                    "R_MAX_meaning": "2 × r_tube 公式值 0.07601（任务书目标半径加倍；顶箱=加倍半径）",
                    "K": K_BINS},
        "taylorDecomposition": {
            "what": "R8-3：Δ_M = M(v)−M(0) 的一阶 sharp K-lift ＋ 二阶提升通道"
                    "（σ_max(J₂) δ-阶梯 × (1−t) 窗口积分），取代 R7-3 的整箱单值 BD2 box 通道",
            "firstOrder": klam_info,
            "secondOrder": {
                "method": "lift：J₂[(k,l),(a,b)] = √(2−δ_kl)√(2−δ_ab)·∂²M_ab/∂v_k∂v_l 的 "
                          "box δ 区间 AD2；σ_max(J₂) 经 K = J₂ᵀJ₂（171×171 稀疏区间）"
                          "λ_max ≤ θ+2‖r‖ 区间 Ritz 认证；dM₂ = R²·∫₀¹(1−t)σ(tR)dt 阶梯分段常数",
                "deltaLadder": [info["delta"] for info in lift_ladder_info],
                "sigmaLadder": [info["sigma"] for info in lift_ladder_info],
                "dmax": mp.nstr(DLIFT, 10),
                "ladderSteps": LIFT_J,
                "appliesToBins": f"k ≤ {K_LIFT_MAX_BIN}（r ≤ {mp.nstr(mp.mpf(bins[K_LIFT_MAX_BIN]), 8)}；"
                                 "更大箱沿用 legacy 均值形式界）",
                "sigmaAtZero": lift_ladder_info[0]["sigma"],
                "sigmaAtDmax": lift_ladder_info[-1]["sigma"],
            },
            "secondOrderLegacyBox": d2_legacy_info,
            "secondOrderJointAlt": joint_info_r,
            "appliesToBins": f"k ≤ {K_LIFT_MAX_BIN}（r ≤ {mp.nstr(mp.mpf(bins[K_LIFT_MAX_BIN]), 8)}；"
                             "更大箱沿用 legacy 均值形式界——σ-阶梯只认证到 δ_max=bin34 测地半径）",
            "legacyR73Archive": {
                **R73_ARCHIVE,
                "note": "R7-3 存档值（字段值冻结为历史对照）。其 BD2 box 通道的 .dd 传播含"
                        "两处规则 bug（bsqrt 第二项对角/交叉 ×2；bdiv 末项 a.v/b² 应为"
                        " a.v/(2b³) 且对称平方键重复累加），实测 .dd 不含真二阶导数"
                        "（含符号翻转，6/6 出界）⟹ 该 d2op=2016.7 与 r*=0.006718398305 "
                        "证书无效；本文件以修复规则复算（secondOrderLegacyBox，同口径"
                        " d2op≈866）并以提升通道重新认证。一阶 klam 不受影响（.d 路径，"
                        "sharp，R8-3 独立复核 12.836 不变）"},
            "advisorySpotChecks": adv_taylor,
            "mechanism": ("R7-3 整箱单值 ½R²·d2op(box) 的两重损失：① box AD 的 .dd 区间宽度在 "
                          "1/r⁵ 链上乘性放大（修复规则后仍 ~7×于点值）；② 全积分以整箱 sup "
                          "付费，而 (1−t) 权重使 t≈0 的小箱主导。R8-3 提升通道：逐 δ 档认证 "
                          "σ_max(J₂)（K=J₂ᵀJ₂ 区间 Ritz，保留 (a,b) 双线性方向耦合——标量解耦"
                          "联合界损失 ~600×，见负对照 e），窗口 [δ_{j−1}/R, δ_j/R]∩[0,1] 取"
                          "窗顶档 σ(δ_j) 的分段常数包络；一阶项不变（K-lift 斜率 "
                          f"{mp.nstr(mp.mpf(klam.b), 6)}）"),
            "validation": "bd_rules_selftest（解析 r⁻¹/r⁻⁵ vs AD 逐键，每次运行）＋advisory 定点采样 "
                          "|u^T(M(v)−M(0)−DM(0)[v])u| ≤ 二阶界（提升＋标量两通道）全部成立（require）"},
        "quadraticGrowth": {
            "rigorousRadius": mp.nstr(r_star, 10),
            "muAtRstar": istr(mu_star),
            "gammaLinear": istr(gamma),
            "deltaOrbitArchive": istr(delta_orb),
            "competitorExclusionRadius": istr(d_excl),
            "omegaSupFormula": "|L0| ≤ (rho_geo²/6)·(3·rho_geo)，|omega| ≤ |L0|/λ_min(rotGram)",
            "pathIntegration": "γ(t)=χ_{X'}(t·w)，X'=Procrustes 最优旋转；"
                               "h''(t)=Hess(u,u)+2Hess(u,ρ)+Hess(ρ,ρ) ≥ μ‖u‖² − cross"},
        "negativeControls": controls,
        "reconciliation": {
            "rTargetFormula": {
                "value": R_TARGET_FORMULA,
                "formula": "sqrt(2·ΔE/λ_ref)；ΔE=4.1535e-4（cap m0748_M8）、"
                           "λ_ref=0.14378982（full_local_min）",
                "recomputedInterval": istr(r_formula),
                "certifiedHere": "否——μ(r=0.07601) 认证区间上端 ≤ 0（bins 顶箱），"
                                 "本方法不可严格化 0.07601；严格半径见 quadraticGrowth.rigorousRadius"},
            "ballScan": {"r=0.076_min": ballscan.get("min"),
                         "r=0.076_mean": ballscan.get("mean"),
                         "note": "tube.json ball_scan（64 随机方向）数值证据：r=0.076 真实 "
                                 "λ_min≈0.0336>0；本文件 advisory 采样（12 方向）见 "
                                 "advisoryNumeric.trueQuotientLambdaSamples——真实正值、证书粗糙"},
            "lambdaChain": {"flm_interval": LAMBDA_REF_FLM,
                            "here_point_cert": lam0_str,
                            "numeric": adv["lambda0Numeric"],
                            "consistent": mp.mpf(lambda0.a) >= mp.mpf(LAMBDA_REF_FLM) - mp.mpf("1e-6")},
            "muKltSplitVerdict": ("任务书 μ_KLT 原式在全部分箱 ≤ 0（" if mu_klt_all_neg else
                                  "警告：μ_KLT 某分箱 > 0（" +
                                  str([b["muKltSplit"] for b in bin_out]) + "）；") +
                                 "p=1/2 常数逆境：正项 (3/4)f_min^{-5/2}·λ ~ 0.5·λ ≲ 1.5，"
                                 "负项 2Σf^{-3/2} ≳ 35——KLT 大 s 论证在 s=1 不适用，"
                                 "刚性正项需逐边配平（本文件 transport 证书即为此）",
            "gapAnalysis": ("证书斜率 ‖Δ_M‖/r（见 bins.deltaMFro/r——谱范数上界）vs 真实 dλ/dr≈1.45"
                            "（ball_scan 0.144→0.0336@0.076）；Frobenius＋区间过估 ~10× ⟹ "
                            "可达严格半径 ~λ₀/斜率 ≪ 0.07601。0.07601 是否真在正性域内是"
                            "数值问题（采样指零点 ≈0.076–0.10），非本证书所能及")},
        "advisoryNumeric": adv,
        "provenance": {
            "seed": SEED, "codeVersion": CODE_VERSION,
            "command": "python3 numerics/bounds/l6_intube.py",
            "ivDps": IV_DPS, "mpDps": MP_DPS, "seriesTerms": N_SER,
            "ladders": {"lambda0": list(LAMBDA0_LADDER), "lambdaS": list(LAMBDA_S_LADDER)},
            "inputs": ["numerics/bounds/local_min.py（R1 机器）",
                       "numerics/bounds/results/local_min.json（z* 存档）",
                       "numerics/bounds/results/full_local_min.json（λ_ref）",
                       "numerics/bounds/results/tube.json（ball_scan、cap ΔE）",
                       "../thomson-workflow/data/energies.json（E*）"],
            "determinism": "无时间戳/运行时字段；固定阶梯常数；sort_keys 序列化；"
                           "重算与存档逐位比对（gate ①）"},
    }
    return result


def istr_parse_hi(s):
    return mp.mpf(s.strip("[]").split(",")[1])


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="KLT §7.4 N=9 tube quadratic growth (L6)")
    ap.add_argument("--out", default=str(DEFAULT_OUT))
    args = ap.parse_args(argv)
    try:
        result = run_certificate()
    except CheckError as e:
        print(f"L6-INTUBE VERIFICATION FAILED: {e}")
        return 1
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(result, ensure_ascii=False, indent=1, sort_keys=True) + "\n"
    if out.exists():
        if out.read_text() != payload:
            print(f"L6-INTUBE ARCHIVE MISMATCH: recomputation differs from {out}")
            return 1
        print(f"archive check: recomputation identical to {out} (gate 1 passed)")
    else:
        out.write_text(payload)
        again = json.dumps(result, ensure_ascii=False, indent=1, sort_keys=True) + "\n"
        require(again == payload, "serialization nondeterminism")
        print(f"archive written (first run): {out}")
    t = result["quadraticGrowth"]
    print(f"lambda0 certified >= {result['lambda0']['certified']}"
          f" (flm {result['lambda0']['fullLocalMinCrosscheck']['value']},"
          f" numeric {result['lambda0']['numeric']})")
    print(f"rigidity: nu6(12) NOT rigid (Maxwell 12<15); S*=nu6+nu2(18) lambda_S0 >= "
          f"{result['rigidity']['edgeSetCertified']['lambdaS0']}, positive self-stress residual "
          f"{result['rigidity']['edgeSetCertified']['positiveSelfStress']['tangentialResidualMaxAbs']}")
    print(f"rigorous tube radius r* = {t['rigorousRadius']} (mu = {t['muAtRstar']})")
    print(f"target 0.07601 certified: "
          f"{result['reconciliation']['rTargetFormula']['certifiedHere'][:60]}...")
    print(f"claim: E(Y) >= Ebar - {t['gammaLinear']}*d + (mu/2)d^2 for d <= {t['rigorousRadius']}")
    print("negative controls: doubleRadius / stressWeight+signFlip / muSignFlip / "
          "channelSwapScalarDecoupled all triggered")
    print(f"L6-INTUBE VERIFICATION OK  ({time.time() - T0WALL:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
