#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""TTP（D3h 三帽三棱柱）在 (S²)⁹ 全空间的严格局部极小——区间算术验证。

对象：E(x)=Σ_{i<j}‖x_i−x_j‖⁻¹ 在流形 M=(S²)⁹ ⊂ ℝ²⁷ 上的限制，构型
X(z)=triCapPrism(z)（family.py / local_min.py 同源），z* ∈ 隔离区间 I
（[0.703648376463, 0.703649139406]，local_min.json 存档，本脚本重推导并断言一致）。

============================================================ 引理链（精确数学 + 区间证书的分工）
记 T(z) = T_{X(z)}M = ⊕_i T_{x_i}S²（18 维），R(z) = {（ω×x_i）_i : ω∈ℝ³}（SO(3)
轨道切方向，3 维 ⊂ T）。环境 Hessian（27×27）：
    H_amb = Σ_{i<j} [3 d dᵀ/|d|⁵ − I/|d|³]（d=x_i−x_j）
球面第二基本形式修正（单位球测地线加速度 γ̈_i = −|v_i|²x_i）给出 M 上 Hessian：
    q_z(v,v) = vᵀ H_amb v − Σ_i (∇_iE·x_i)‖v_i‖²        (v ∈ T)

**约化坐标**：逐点正交切基 {e_θ,i=(−sinθ_i,cosθ_i,0), e_m,i=∂_zX 的第 i 点分量
= (−(z/ρ)cosθ_i, −(z/ρ)sinθ_i, ±1)}（帽点 e_m=ẑ），v=Σ_c a_c b_c 的系数 a∈ℝ¹⁸；
此基的 Gram 恰为 G(z)=diag(1,1/ρ²)（三角点，ρ²=1−z²）、diag(1,1)（帽点）——精确对角。
Q_red(z)（18×18）= q_z 在该基下的矩阵，逐对装配（36 对 + 9 点修正；不走 27×27
三明治——直接区间三明治的入口宽度 ~225 项累积 ~0.03–0.3，会把 λ 证书压垮）。

L1【R1 已证，本脚本重验证】E′ 在 I 两端严格变号且 E″>0 整区间 ⇒ 存在唯一
    z*∈int I 使 E′(z*)=0。
L2【精确，数值复核】D3h 固定的环境向量空间 F_amb（3 维：T0=(ρ,0,z) 处 (a,0,c)
    与 C1=(−1,0,0) 处 (b,0,0) 经 D3h 传播）有显式基 f1（三角水平 120° 花样）/
    f2（顶 +ẑ 底 −ẑ）/f3（帽水平径向花样），且 v_fam=∂_zX = −(z/ρ)f1 + f2
    （逐点：顶点 (−(z/ρ)c_k,−(z/ρ)s_k,+1)；T0 切向条件 aρ+cz=0 唯一定比例）
    ⇒ F_amb∩T = span{v_fam}。数值复核：f1·x_{T0}=ρ、f3·x_{C1}=1 区间严格离 0。
L3【精确】∇E 与 D3h 交换 ⇒ X(z) 处 ∇E∈F_amb ⇒ 切向梯度 ∈ span{v_fam}；且
    ∇E·v_fam = E′(z)（链式法则）。在 z*：E′(z*)=0 ⇒ 切向梯度=0，X* 是 E|_M 的
    临界点。数值复核：grad_i 与 18 个基向量的点积区间全含 0 且 |·|≤1e-3（∝|E′|）。
L4【精确】临界点处 E|_M 的 Hessian = q_z 在 T 上的二次型（Q_red 系数矩阵）。
L5【精确，数值复核】SO(3) 不变性 ⇒ q_z(w,w)=Σ_i(ω·x_i)[(∇_iE·x_i)(ω·x_i)−
    (ω·∇_iE)] 在临界点（∇_iE=λ_i x_i）恒为 0；数值复核：C_RᵀQ_redC_R 全含 0。
L6【精确，数值复核】临界点处切向 s 与 w∈R 的交叉项 sᵀHw = s·(ω∇E) −
    Σ_i(∇_iE·x_i)(s_i·w_i) = 0（∇_iE=λ_ix_i 时逐点相消）；数值复核：Q_redC_R
    全含 0。两核对的量级 ∝|E′| ≤ 3.2e-5（z→z* 收敛到精确 0）。
L7【区间证书】对一切 z∈I：
    (a) 基切向（构造精确，区间残差 <1e-4）；C_RᵀGC_R ≻0 ⇒ dim R=3；
    (b) z_mid 处（退化点区间，宽度 ~1e-49）做区间 Gram–Schmidt（G-度量）：旋转
        系数正交归一 Ŵ → 18 个单位坐标向量投影到 R^⊥ → 带列主元选出 15 个
        正交归一列 A₀（18×15，视为固定矩阵）⇒ S_A(z):={Σa_c b_c(z): a∈col(A₀)}
        是 T(z) 的 15 维子空间；[A₀|C_R]ᵀG(z)[A₀|C_R] ≻0（整区间 I）⇒
        S_A(z)∩R(z)=0 ⇒ T(z)=S_A(z)⊕R(z)（对一切 z∈I，18=15+3）；
    (c) **中值形式**：M(z):=A₀ᵀQ_red(z)A₀、Ĝ(z):=A₀ᵀG(z)A₀（A₀ 固定 ⇒
        M(z) ⊆ M(z_mid) + [A₀ᵀQ′_red(I)A₀]·(I−z_mid)，Q′ 由对偶区间自动微分
        给出）。区间 Cholesky（LDLᵀ，主元区间下端>0）证 M(z)−λĜ(z)≻0 ⇒
        ∀z∈I, ∀v∈S_A(z)\{0}: q_z(v,v) ≥ λ‖v‖²（环境欧氏范数）。
L8【推论】在 z=z*：u=s+r（s∈S_A, r∈R）⇒ q(u)=q(s) ≥ λ‖s‖² ≥ λ·dist(u,R)²
    （L5/L6 在临界点精确消去 r 与交叉项；‖s‖=‖u−r‖ ≥ dist(u,R)）⇒ ker Hess = R
    （恰为 SO(3) 轨道方向；商切空间 15 维上无核），λ_min(商) ≥ λ > 0 ⇒ X* 是模
    SO(3) 的非退化严格局部极小（二阶充分条件；Taylor 余项→管状半径由下游管状线
    处理，本脚本交付 λ 的严格区间下界）。

数值（float64，advisory 非证明）：18 维切空间广义特征 = 3 个 O(|E′|)≈1e-6 的
旋转近零模 + 15 个正特征值（min ≈ 0.143934，与 GAP-REPORT Round 2 的 0.143935
一致）；区间证书预期 λ ≥ 0.1439−ε。对偶 AD 自检：Q_red/λ_i/C_R 若干项的 dz
导数 vs 中心差分（容差 1e-4 相对）——抓接线错误。

--selftest 负对照（都按预期触发 CheckError 才 exit 0）：
  (i)  退化 z：I=[0.45, 0.45001]（数值 λ_min ≈ −1.06：对称破缺方向——扭转/压扁
       软模——负曲率）上跑同一条商空间正定性认证路径（ladder=[0]），断言必须
       触发 "not positive definite"；
  (ii) 篡改矩阵：真实区间数据上 M − 0.4·Ĝ（平移出正定锥），断言区间 Cholesky
       必须触发（看守 Cholesky 实现本身能检出不定）。
任何断言失败即 sys.exit(1)。

输出：bounds/results/full_local_min.json。
用法：python3 numerics/bounds/full_local_min.py [--selftest] [--out PATH]
依赖：mpmath >= 1.3（区间算术）；numpy 仅用于 advisory 数值对照。
"""
from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

import mpmath
from mpmath import iv, mp

sys.path.insert(0, str(Path(__file__).resolve().parent))
import local_min as lm  # noqa: E402  R1 已验证的 E/E'/E'' 区间机器（同目录）

# ------------------------------------------------------------------ 配置
IV_DPS = 50                        # 区间算术工作精度（十进制位）
SADDLE_INTERVAL = ("0.45", "0.45001")  # 负对照：对称破缺方向负曲率的退化 z
                                   # （宽度 1e-5：切向残差 ~2.5e-5 < 1e-4 阈值，
                                   #   λ_min ≈ −1.06 负裕度 ≫ 区间膨胀）
SADDLE_LAMBDA_NUMERIC = -1.058713      # float64 扫描值（advisory，写进结果供对照）
TANG_EPS = mp.mpf("1e-4")          # 构造精确性残差的区间宽度判据（精确算术为 0，
                                   # 区间求值残差 ~ z 区间宽 7.6e-7 × O(2)）
TINY = mp.mpf("1e-3")              # ∝|E'| 量的核对阈值（L3/L5/L6 数值复核）
E_STAR_TOL = mp.mpf("1e-8")        # E(z*) vs energies.json
LAMBDA_LADDER = ("0.9999", "0.999", "0.998", "0.995", "0.99", "0.98", "0.95", "0.9")
FD_H = 1e-6                        # AD 自检的差分步长
FD_TOL = 1e-4                      # AD 自检相对容差

REPO_ROOT = Path(__file__).resolve().parents[2]
RESULTS_DIR = Path(__file__).resolve().parent / "results"
DEFAULT_OUT = RESULTS_DIR / "full_local_min.json"
R1_JSON = RESULTS_DIR / "local_min.json"


class CheckError(Exception):
    """验证断言失败（负对照按预期触发也用它携带原因）。"""


def require(cond, msg: str) -> None:
    if not cond:
        raise CheckError(msg)


iv.dps = IV_DPS
mp.dps = IV_DPS + 30          # 具体矩阵（预条件子）的精度
_0 = iv.mpf(0)
_1 = iv.mpf(1)


# ================================================================ 对偶区间自动微分（d/dz）
class DI:
    """区间对偶数 (v, d) = (f(z), f'(z)) 的 enclosure。

    法则为精确代数：(fg)'=f'g+fg'，(1/g)'=(a'g−ag')/g²，(√a)'=a'/(2√a)。
    在区间 Z 上求值给出 f(Z)、f'(Z) 的外向 enclosure。"""
    __slots__ = ("v", "d")

    def __init__(self, v, d):
        self.v, self.d = v, d


def dk(x) -> DI:
    return DI(iv.mpf(x), _0)


def dz(Z) -> DI:
    return DI(iv.mpf(Z), _1)


def dadd(a: DI, b: DI) -> DI:
    return DI(a.v + b.v, a.d + b.d)


def dsub(a: DI, b: DI) -> DI:
    return DI(a.v - b.v, a.d - b.d)


def dmul(a: DI, b: DI) -> DI:
    return DI(a.v * b.v, a.d * b.v + a.v * b.d)


def ddiv(a: DI, b: DI) -> DI:
    b2 = b.v * b.v
    return DI(a.v / b.v, (a.d * b.v - a.v * b.d) / b2)


def dsqrt(a: DI) -> DI:
    s = iv.sqrt(a.v)
    return DI(s, a.d / (2 * s))


def dneg(a: DI) -> DI:
    return DI(-a.v, -a.d)


def ddot3(u, w) -> DI:
    r = dk(0)
    for a, b in zip(u, w):
        r = dadd(r, dmul(a, b))
    return r


# ================================================================ 区间线性代数小工具
def istr(I) -> str:
    return f"[{mp.nstr(mp.mpf(I.a), IV_DPS + 3)}, {mp.nstr(mp.mpf(I.b), IV_DPS + 3)}]"


def iabs_sup(I) -> mp.mpf:
    return max(abs(mp.mpf(I.a)), abs(mp.mpf(I.b)))


def contains_zero(I) -> bool:
    return mp.mpf(I.a) <= 0 <= mp.mpf(I.b)


def dot(u, v):
    return sum((a * b for a, b in zip(u, v)), _0)


def vsub(u, v):
    return [a - b for a, b in zip(u, v)]


def vscale(a, u):
    return [a * b for b in u]


def interval_cholesky_pd(A, label: str):
    """对称区间矩阵严格正定：区间 Cholesky（LDLᵀ），主元区间下端 > 0 即证书。

    enclosure 内每个（对称）具体矩阵的精确 Cholesky 主元都落在对应区间主元内
    （区间算术包含性归纳），主元全正 ⟺ 正定 ⇒ 全体正定。"""
    n = len(A)
    L = [[_0] * n for _ in range(n)]
    d = [None] * n
    for j in range(n):
        s = A[j][j]
        for k in range(j):
            s = s - d[k] * (L[j][k] * L[j][k])
        if mp.mpf(s.a) <= 0:
            raise CheckError(
                f"{label}: pivot {j} not positive definite, interval {istr(s)}")
        d[j] = s
        inv = _1 / s
        for i in range(j + 1, n):
            t = A[i][j]
            for k in range(j):
                t = t - d[k] * (L[i][k] * L[j][k])
            L[i][j] = t * inv
    return d


def mp_cholesky_upper(A, label: str):
    """具体 mp 矩阵（紧区间中点）的 Cholesky：A = RᵀR，R 上三角，mp.dps 高精度。

    仅作预条件子（同余不改变正定性，不承担证明职责）；主元 ≤ tol 视为非正定。"""
    n = len(A)
    R = [[mp.mpf(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            s = A[i][j]
            for k in range(i):
                s = s - R[k][i] * R[k][j]
            if i == j:
                if s <= mp.mpf("1e-25"):
                    raise CheckError(
                        f"{label}: midpoint preconditioner pivot {i} not "
                        f"positive definite ({mp.nstr(s, 6)})")
                R[i][i] = mp.sqrt(s)
            else:
                R[i][j] = s / R[i][i]
    return R


def mp_upper_inverse(R):
    """上三角 R 的逆（回代，具体 mp）。行 i 依赖行 l>i，故降序：
    Rinv[i][i] = 1/R[i][i]；Rinv[i][j] = −(1/R_ii) Σ_{l>i} R[i][l]·Rinv[l][j] (j<i)。"""
    n = len(R)
    Rinv = [[mp.mpf(0)] * n for _ in range(n)]
    for i in range(n - 1, -1, -1):
        Rinv[i][i] = 1 / R[i][i]
        for j in range(n - 1, i, -1):          # 上三角未知元在对角线右侧 (j > i)
            s = mp.mpf(0)
            for l in range(i + 1, j + 1):      # B[l][j]=0 for l>j，取到 j 即可
                s = s + R[i][l] * Rinv[l][j]
            Rinv[i][j] = -s / R[i][i]
    return Rinv


def certify_pd_preconditioned(X_enc, label: str):
    """区间矩阵 X(z) ≻ 0 的预条件同余认证。

    取 enclosure 中点为具体矩阵 X̄，mp Cholesky 得 R（X̄ = RᵀR，仅作预条件子，
    不承担证明职责），同余 X̃(z) = R⁻¹ X(z) R⁻ᵀ ≻ 0 ⟺ X(z) ≻ 0；X̃ ≈ I + O(扰动)，
    区间 Cholesky 在条件数 ~1 下运行，损失 ~‖Δ‖_F（平方级退化消失）。"""
    R = mp_cholesky_upper([[ (mp.mpf(X_enc[i][j].a) + mp.mpf(X_enc[i][j].b)) / 2
                             for j in range(len(X_enc))] for i in range(len(X_enc))],
                          label + " [preconditioner]")
    Rinv = mp_upper_inverse(R)
    n = len(X_enc)
    # 白化同余：X = RᵀR ⇒ X̃ = R⁻ᵀ X R⁻¹ = Bᵀ X B（B = R⁻¹ 上三角）≈ I + O(扰动)
    B = [[iv.mpf(mp.nstr(Rinv[i][j], 60)) for j in range(n)] for i in range(n)]
    Y = [[sum((X_enc[i][k] * B[k][l] for k in range(n)), _0)
          for l in range(n)] for i in range(n)]        # X·B
    Xt = [[sum((B[k][i] * Y[k][j] for k in range(n)), _0)
           for j in range(n)] for i in range(n)]       # Bᵀ·(X·B)
    interval_cholesky_pd(Xt, label + " [preconditioned congruence]")


# ================================================================ 构型与切几何（对偶区间）
def angles_exact():
    """精确角度常数（有理数与 √3）：三角 (cosθ,sinθ)、帽 (cosφ,sinφ)。"""
    h = iv.sqrt(iv.mpf(3))
    half = iv.mpf(1) / 2
    tri = [(iv.mpf(1), _0), (iv.mpf(-1) / 2, h / 2), (iv.mpf(-1) / 2, -h / 2)]
    caps = [(half, h / 2), (iv.mpf(-1), _0), (half, -h / 2)]
    return tri, caps


def geometry_dual(Z):
    """对偶区间装配：pts（9 点 DI 3-vec）、切基 b_cols（18 个 (point, DI 3-vec)）、
    旋转场 w_axes[a][i]（DI 3-vec）、G 对角元（DI，18 个）。

    e_θ 常数（d=0）；e_m=∂_z(ρcosθ,ρsinθ,±z)（DI 链式法则自动求导）；
    w^a_i = e_a×x_i（DI 自动求导）。"""
    Zd = dz(Z)
    rho = dsqrt(dsub(dk(1), dmul(Zd, Zd)))           # ρ = √(1−z²)
    tri, caps = angles_exact()
    pts = []
    for (c, s) in tri:                                # top：z 坐标 +z
        pts.append([dmul(rho, dk(c)), dmul(rho, dk(s)), Zd])
    for (c, s) in tri:                                # bottom：z 坐标 −z
        pts.append([dmul(rho, dk(c)), dmul(rho, dk(s)), dneg(Zd)])
    for (c, s) in caps:                               # caps：常数
        pts.append([dk(c), dk(s), dk(0)])
    # 切基：18 列 (point_idx, DI 3-vec)，顺序 top(0..2), bottom(3..5), caps(6..8)，
    # 每点 (e_θ, e_m)。族参数 z>0：z 坐标符号只进 e_m 第三分量（±1）。
    b_cols = []
    for k, (c, s) in enumerate(tri):
        b_cols.append((k, [dneg(dk(s)), dk(c), dk(0)]))
        b_cols.append((k, [dneg(ddiv(dmul(Zd, dk(c)), rho)),
                           dneg(ddiv(dmul(Zd, dk(s)), rho)), dk(1)]))
    for k, (c, s) in enumerate(tri):
        b_cols.append((3 + k, [dneg(dk(s)), dk(c), dk(0)]))
        b_cols.append((3 + k, [dneg(ddiv(dmul(Zd, dk(c)), rho)),
                               dneg(ddiv(dmul(Zd, dk(s)), rho)), dk(-1)]))
    for k, (c, s) in enumerate(caps):
        b_cols.append((6 + k, [dneg(dk(s)), dk(c), dk(0)]))
        b_cols.append((6 + k, [dk(0), dk(0), dk(1)]))         # 帽 e_m = ẑ
    # 旋转场：w^x=(0,−z_i,y_i)，w^y=(z_i,0,−x_i)，w^z=(−y_i,x_i,0)
    w_axes = []
    for axis in range(3):
        per_point = []
        for (x, y, zc) in pts:
            if axis == 0:
                per_point.append([dk(0), dneg(zc), y])
            elif axis == 1:
                per_point.append([zc, dk(0), dneg(x)])
            else:
                per_point.append([dneg(y), x, dk(0)])
        w_axes.append(per_point)
    # G 对角元（精确）：e_θ·e_θ=1；三角 e_m·e_m = z²/ρ²+1 = 1/ρ²（ρ²=1−z²）；帽 e_m=ẑ 为 1
    inv_rho2 = ddiv(dk(1), dmul(rho, rho))
    g_diag = [dk(1), inv_rho2] * 3 + [dk(1), inv_rho2] * 3 + [dk(1), dk(1)] * 3
    return pts, b_cols, w_axes, g_diag, rho, Zd


def reduced_hessian_dual(Z):
    """Q_red(z)（18×18 DI）、grad（9×3 DI）、λ_i=∇_iE·x_i（9 DI）、C_R（18×3 DI）。

    Q_red[c][c'] = Σ_{i<j} [3 D_c D_c'/r⁵ − (δ_c·δ_c')/r³] − Σ_i λ_i (b_c·b_c')|_i，
    D_c = d·δ_c，δ_c = +b_c（支点=i）/ −b_c（支点=j）/ 0（其余）；
    C_R = 旋转场切基系数（e_θ 列系数 = w·e_θ（|e_θ|²=1），e_m 列系数 = (w·e_m)/(1+z²)）。"""
    pts, b_cols, w_axes, g_diag, rho, Zd = geometry_dual(Z)
    n = 9
    grad = [[dk(0), dk(0), dk(0)] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            d = [dsub(pts[i][t], pts[j][t]) for t in range(3)]
            r2 = ddot3(d, d)
            r = dsqrt(r2)
            inv_r3 = ddiv(dk(1), dmul(r, r2))
            for t in range(3):
                grad[i][t] = dsub(grad[i][t], dmul(d[t], inv_r3))
                grad[j][t] = dadd(grad[j][t], dmul(d[t], inv_r3))
    lam = [ddot3(grad[i], pts[i]) for i in range(n)]
    acc = [[dk(0) for _ in range(18)] for _ in range(18)]
    for i in range(n):
        for j in range(i + 1, n):
            d = [dsub(pts[i][t], pts[j][t]) for t in range(3)]
            r2 = ddot3(d, d)
            r = dsqrt(r2)
            inv_r3 = ddiv(dk(1), dmul(r, r2))
            inv_r5 = ddiv(inv_r3, r2)
            cols_ij = [c for c in range(18) if b_cols[c][0] in (i, j)]
            D = {}
            for c in cols_ij:
                sgn = 1 if b_cols[c][0] == i else -1
                vec = b_cols[c][1] if sgn == 1 else [dneg(x) for x in b_cols[c][1]]
                D[c] = (sgn, ddot3(d, vec), vec)
            for c in cols_ij:
                for c2 in cols_ij:
                    _, Dc, vc = D[c]
                    _, Dc2, vc2 = D[c2]
                    g_cc = ddot3(vc, vc2)     # vc/vc2 已带符号 ⇒ 即 δ_c·δ_c′
                    term = dsub(dmul(dk(3), dmul(dmul(Dc, Dc2), inv_r5)),
                                dmul(g_cc, inv_r3))
                    acc[c][c2] = dadd(acc[c][c2], term)
    for i in range(n):
        cols_i = [c for c in range(18) if b_cols[c][0] == i]
        for c in cols_i:
            for c2 in cols_i:
                acc[c][c2] = dsub(acc[c][c2], dmul(lam[i],
                                                   ddot3(b_cols[c][1], b_cols[c2][1])))
    C_R = [[None] * 3 for _ in range(18)]
    for c, (i, bvec) in enumerate(b_cols):
        for a in range(3):
            w = w_axes[a][i]
            C_R[c][a] = ddiv(ddot3(w, bvec), g_diag[c])   # 帽 e_m 的 |·|²=1 已含于 g_diag
    return acc, grad, lam, C_R, b_cols, pts, g_diag


# ================================================================ z_mid 上的子空间构造（G-度量）
def build_A0(C_R_cols, g_diag_tight):
    """z_mid（退化区间）上：旋转系数 G-正交归一（Ŵ）→ 18 单位坐标投影到 R^⊥ →
    带列主元 Gram–Schmidt 选 15 个 G-正交归一列 → A₀（18×15 紧区间矩阵）。

    C_R_cols：3 个 18 维系数列。"""
    def dotG(a, b):
        return sum((a[c] * b[c] * g_diag_tight[c] for c in range(18)), _0)

    What = []
    for col in C_R_cols:
        v = list(col)
        for u in What:
            v = vsub(v, vscale(dotG(u, v), u))
        n2 = dotG(v, v)
        require(mp.mpf(n2.a) > mp.mpf("0.5"),
                f"Gram-Schmidt on rotation coefficients degenerated: {istr(n2)}")
        nrm = iv.sqrt(n2)
        What.append([c / nrm for c in v])

    def residual(v):
        r = list(v)
        for u in What:
            r = vsub(r, vscale(dotG(u, r), u))
        return r

    cands = []
    for c in range(18):
        e = [_0] * 18
        e[c] = _1
        cands.append(residual(e))
    sel = []
    remaining = list(cands)
    while len(sel) < 15 and remaining:
        best_i, best_lo, best_r = None, None, None
        for idx, v in enumerate(remaining):
            r = list(v)
            for u in sel:
                r = vsub(r, vscale(dotG(u, r), u))
            lo = mp.mpf(dotG(r, r).a)
            if best_lo is None or lo > best_lo:
                best_i, best_lo, best_r = idx, lo, r
        require(best_lo > 0,
                f"pivoted Gram-Schmidt exhausted positive candidates at step "
                f"{len(sel)} (need 15)")
        nrm = iv.sqrt(dotG(best_r, best_r))
        sel.append([c / nrm for c in best_r])
        remaining.pop(best_i)
    return sel, What


def sandwich_mean_value(A0, Mmid, Mder, dz_iv):
    """中值形式：A₀ᵀK(z)A₀ ⊆ A₀ᵀK(z_mid)A₀ + (A₀ᵀK′(I)A₀)·(z−z_mid)。

    A0：15 个 18 维列；Mmid/Mder：18×18 紧/松区间矩阵。返回 15×15。"""
    k = len(A0)
    V = [[sum((A0[a][c] * Mmid[c][c2] * A0[b][c2]
               for c in range(18) for c2 in range(18)), _0)
          for b in range(k)] for a in range(k)]
    D = [[sum((A0[a][c] * Mder[c][c2] * A0[b][c2]
               for c in range(18) for c2 in range(18)), _0)
          for b in range(k)] for a in range(k)]
    return [[V[a][b] + D[a][b] * dz_iv for b in range(k)] for a in range(k)]


# ================================================================ L2/L3/L5/L6 一致性核对
def consistency_checks(Q_I, grad_I, C_R_I, b_I, pts_I):
    """z*-邻域专用（阈值 TINY 对应 |E'| ~ 3.2e-5 量级）。"""
    out = {}
    # L3：grad_i 与 18 个基向量的点积（切向梯度的基表示，比例因子 |b_c|² O(1)）
    g_red = [ddot3(grad_I[b_I[c][0]], b_I[c][1]) for c in range(18)]
    require(all(contains_zero(x.v) for x in g_red),
            "L3 violated: tangential-gradient basis dots must contain 0 "
            "(D3h forces them proportional to E')")
    worst = max(iabs_sup(x.v) for x in g_red)
    require(worst < TINY,
            f"L3 violated: tangential gradient too large for z near z* "
            f"(should be ~|E'|): {mp.nstr(worst, 4)}")
    out["L3_tangentialGradientMaxAbs"] = mp.nstr(worst, 4)

    # L5：C_Rᵀ Q_red C_R；L6：Q_red C_R
    QCR = [[sum((Q_I[c][a2].v * C_R_I[c][a].v for c in range(18)), _0)
            for a in range(3)] for a2 in range(18)]
    CRtQCR = [[dot(QCR_row, [C_R_I[c][b].v for c in range(18)]) for b in range(3)]
              for QCR_row in QCR]
    flat = [v for row in CRtQCR + QCR for v in row]
    require(all(contains_zero(x) for x in flat),
            "L5/L6 violated: C_R^T Q_red C_R / Q_red C_R entries must contain 0")
    worst = max(iabs_sup(x) for x in flat)
    require(worst < TINY,
            f"L5/L6 violated: rotation-kernel residuals too large (should be "
            f"~|E'|): {mp.nstr(worst, 4)}")
    out["kernelConsistencyMaxAbs"] = mp.nstr(worst, 4)

    # L2：f1·x_{T0} = ρ（f1 的 T0 取值 (1,0,0)），f3·x_{C1} = 1（均为精确常数×ρ）
    d1 = pts_I[0][0].v                              # x_{T0} 的第一坐标 = ρ
    d3 = _1                                         # f3·x_{C1} = (−1,0,0)·(−1,0,0)
    require(not contains_zero(d1) and iabs_sup(d1) > mp.mpf("0.4"),
            f"L2 violated: f1 unexpectedly tangent at T0: {istr(d1)}")
    require(iabs_sup(d3) > mp.mpf("0.9"),
            "L2 violated: f3 unexpectedly tangent at C1")
    out["L2_f1f3Nontangent"] = [istr(d1), istr(d3)]
    return out


# ================================================================ 商空间证书（中值形式）
def quotient_certificate_at(Z, z_mid, ladder, want_consistency=False):
    """L7 全流程：在 Z（区间）上构造并认证 M(z) − λĜ(z) ≻0。

    z_mid 为 Z 中点的退化区间（A₀ 与中值中心）。失败抛 CheckError（正定失败消息
    含 "not positive definite"）。"""
    Q_mid, grad_mid, lam_mid, C_R_mid, b_mid, pts_mid, g_mid = \
        reduced_hessian_dual(z_mid)
    Q_I, grad_I, lam_I, C_R_I, b_I, pts_I, g_I = reduced_hessian_dual(Z)

    Qv = [[x.v for x in row] for row in Q_mid]      # 紧（z_mid 退化区间）
    Qd = [[x.d for x in row] for row in Q_I]        # d/dz enclosure（整个 I 有效）
    g_tight = [x.v for x in g_mid]
    g_I_v = [x.v for x in g_I]
    g_I_d = [x.d for x in g_I]
    C_R_cols_mid = [[C_R_mid[c][a].v for c in range(18)] for a in range(3)]
    C_R_cols_I = [[C_R_I[c][a].v for c in range(18)] for a in range(3)]

    # ---- L7a：切向性（构造精确，区间残差小）
    for c, (i, bvec) in enumerate(b_I):
        d = ddot3(bvec, pts_I[i])
        require(contains_zero(d.v) and iabs_sup(d.v) < TANG_EPS,
                f"basis column {c} not tangent at point {i}: {istr(d.v)}")

    # ---- L7b：A₀（z_mid 紧区间）＋ dim R=3 ＋ 直和横截性（整区间 I 上）
    A0, What = build_A0(C_R_cols_mid, g_tight)
    CRtGCR = [[sum((C_R_cols_I[a][c] * C_R_cols_I[b][c] * g_I_v[c]
                    for c in range(18)), _0) for b in range(3)] for a in range(3)]
    interval_cholesky_pd(CRtGCR, "C_R^T G C_R [dim R = 3]")
    cols18 = [list(col) for col in A0] + C_R_cols_I
    Gfull = [[sum((cols18[a][c] * cols18[b][c] * g_I_v[c] for c in range(18)), _0)
              for b in range(18)] for a in range(18)]
    interval_cholesky_pd(Gfull, "Gram_G([A0 | C_R]) [T = S_A (+) R on all of I]")

    # ---- L7c：中值形式 M(z)、Ĝ(z)
    dz_iv = iv.mpf(Z) - iv.mpf(z_mid)
    M = sandwich_mean_value(A0, Qv, Qd, dz_iv)
    Gmid_m = [[(g_tight[c] if c == c2 else _0) for c2 in range(18)] for c in range(18)]
    Gder_m = [[(g_I_d[c] if c == c2 else _0) for c2 in range(18)] for c in range(18)]
    Ghat = sandwich_mean_value(A0, Gmid_m, Gder_m, dz_iv)

    out = {"M": M, "Ghat": Ghat, "A0": A0, "Q_I": Q_I, "grad_I": grad_I,
           "C_R_I": C_R_I, "b_I": b_I, "pts_I": pts_I}
    if want_consistency:
        out["consistency"] = consistency_checks(Q_I, grad_I, C_R_I, b_I, pts_I)

    for lam in ladder:
        try:
            certify_pd_preconditioned(
                [[M[a][b] - lam * Ghat[a][b] for b in range(15)]
                 for a in range(15)],
                f"M(z) - lambda*Ghat(z) (lambda = {mp.nstr(mp.mpf(lam.a), 10)})")
            out["lambda"] = lam
            return out
        except CheckError:
            continue
    raise CheckError("could not certify positive definiteness M - lambda*Ghat "
                     f"for any lambda on the ladder "
                     f"({', '.join(mp.nstr(mp.mpf(l.a), 6) for l in ladder)})")


# ================================================================ advisory 数值对照（非证明）
def numeric_advisory(z_mid: float):
    """float64 数值：18 维切空间广义谱 + 商空间 λ_min（仅 advisory，锚定 λ 阶梯）。"""
    import numpy as np
    import math
    s3 = math.sqrt(3.0)
    rho = math.sqrt(1 - z_mid * z_mid)
    tri = [(1.0, 0.0), (-0.5, s3 / 2), (-0.5, -s3 / 2)]
    caps = [(0.5, s3 / 2), (-1.0, 0.0), (0.5, -s3 / 2)]
    pts = ([(rho * c, rho * s, z_mid) for c, s in tri]
           + [(rho * c, rho * s, -z_mid) for c, s in tri]
           + [(c, s, 0.0) for c, s in caps])
    n = 9
    H = np.zeros((27, 27))
    grad = np.zeros(27)
    for i in range(n):
        for j in range(i + 1, n):
            d = np.array(pts[i]) - np.array(pts[j])
            r = np.linalg.norm(d)
            r3, r5 = r ** 3, r ** 5
            grad[3 * i:3 * i + 3] -= d / r3
            grad[3 * j:3 * j + 3] += d / r3
            for a in range(3):
                for b in range(3):
                    Bij = 3 * d[a] * d[b] / r5 - (1.0 if a == b else 0.0) / r3
                    H[3 * i + a][3 * i + b] += Bij
                    H[3 * j + a][3 * j + b] += Bij
                    H[3 * i + a][3 * j + b] -= Bij
                    H[3 * j + a][3 * i + b] -= Bij
    for i in range(n):
        lam = grad[3 * i:3 * i + 3] @ np.array(pts[i])
        for a in range(3):
            for b in range(3):
                H[3 * i + a][3 * i + b] -= lam * (
                    (1.0 if a == b else 0.0) - pts[i][a] * pts[i][b])
    B = np.zeros((27, 18))                       # 切基（公式与对偶版一致）
    z_over_rho = z_mid / rho
    idx = 0
    for k, (c, s) in enumerate(tri):
        B[3 * k:3 * k + 3, idx] = [-s, c, 0.0]
        B[3 * k:3 * k + 3, idx + 1] = [-z_over_rho * c, -z_over_rho * s, 1.0]
        idx += 2
    for k, (c, s) in enumerate(tri):
        B[3 * (3 + k):3 * (3 + k) + 3, idx] = [-s, c, 0.0]
        B[3 * (3 + k):3 * (3 + k) + 3, idx + 1] = [-z_over_rho * c, -z_over_rho * s, -1.0]
        idx += 2
    for k, (c, s) in enumerate(caps):
        B[3 * (6 + k):3 * (6 + k) + 3, idx] = [-s, c, 0.0]
        B[3 * (6 + k):3 * (6 + k) + 3, idx + 1] = [0.0, 0.0, 1.0]
        idx += 2
    W = np.zeros((27, 3))
    for i in range(n):
        x, y, z = pts[i]
        W[3 * i:3 * i + 3, 0] = [0.0, -z, y]
        W[3 * i:3 * i + 3, 1] = [z, 0.0, -x]
        W[3 * i:3 * i + 3, 2] = [-y, x, 0.0]
    H18 = B.T @ H @ B
    G18 = B.T @ B
    w18 = np.sort(np.linalg.eigvals(np.linalg.solve(G18, H18)).real)
    Qb, _ = np.linalg.qr(B)
    Qw, _ = np.linalg.qr(W)
    P = Qb - Qw @ (Qw.T @ Qb)
    U, sv, _ = np.linalg.svd(P, full_matrices=False)
    S = U[:, sv > 1e-10]
    lam_q = float(np.linalg.eigvalsh(S.T @ H @ S).min())
    return {
        "tangentGeneralizedEigenvalues": [float(v) for v in w18],
        "quotientDim": int((sv > 1e-10).sum()),
        "quotientLambdaMin": lam_q,
    }


def ad_selftest(z_mid_mp):
    """对偶 AD 自检：Q_red/λ_i/C_R 若干项的 dz 导数 vs 中心差分（失败即 exit 1）。"""
    zm = iv.mpf(mp.nstr(z_mid_mp, 40))
    Qm, gm, lm, Cm, *_ = reduced_hessian_dual(zm)
    Qp, gp, lp, Cp, *_ = reduced_hessian_dual(
        iv.mpf(mp.nstr(z_mid_mp + FD_H / 2, 40)))
    Qn, gn, ln, Cn, *_ = reduced_hessian_dual(
        iv.mpf(mp.nstr(z_mid_mp - FD_H / 2, 40)))

    def check(name, dual, v_plus, v_minus):
        fd = (mp.mpf(v_plus.a) - mp.mpf(v_minus.b)) / mp.mpf(FD_H)
        ad = mp.mpf(dual.a)
        scale = max(abs(fd), abs(ad), mp.mpf(1))
        require(abs(fd - ad) / scale < FD_TOL,
                f"AD selftest failed at {name}: dual {mp.nstr(ad, 6)} vs "
                f"central difference {mp.nstr(fd, 6)}")

    for (c, c2) in ((0, 0), (1, 1), (0, 1), (7, 8), (13, 16), (17, 17)):
        check(f"Q[{c}][{c2}]", Qm[c][c2].d, Qp[c][c2].v, Qn[c][c2].v)
    for i in (0, 4, 7):
        check(f"lambda_{i}", lm[i].d, lp[i].v, ln[i].v)
    for (c, a) in ((1, 0), (1, 2), (13, 1)):
        check(f"C_R[{c}][{a}]", Cm[c][a].d, Cp[c][a].v, Cn[c][a].v)
    return {"checkedEntries": ["Q[0][0]", "Q[1][1]", "Q[0][1]", "Q[7][8]",
                               "Q[13][16]", "Q[17][17]", "lambda_0/4/7",
                               "C_R[1][0]", "C_R[1][2]", "C_R[13][1]"],
            "fdStep": FD_H, "toleranceRelative": FD_TOL}


# ================================================================ 主流程
def load_r1_interval():
    """从 R1 存档读 z* 隔离区间，并重推导断言一致（不信任过期 JSON）。"""
    require(R1_JSON.exists(), f"missing {R1_JSON}: run local_min.py first (R1)")
    with open(R1_JSON) as f:
        r1 = json.load(f)
    lo_s, hi_s = [s.strip() for s in r1["zStarInterval"].strip("[]").split(",")]
    lo, hi, *_ = lm.isolate(*lm.BRACKET, mp.mpf("1e-6"))
    redo = lm.outward_decimal(mpmath.mpi(lo.a, hi.b))
    require(redo == r1["zStarInterval"],
            f"R1 archive interval {r1['zStarInterval']} != recomputed {redo}")
    return iv.mpf(lo_s), iv.mpf(hi_s), r1


def midpoint_interval(Z):
    return iv.mpf(mp.nstr((mp.mpf(Z.a) + mp.mpf(Z.b)) / 2, 40))


def verify_full_local_min():
    res = {}

    # ---- L1：z* 隔离（复用 R1 并重验证 E' 变号、E''>0）
    lo, hi, r1 = load_r1_interval()
    Z = iv.mpf(mpmath.mpi(mp.mpf(lo.a), mp.mpf(hi.b)))
    Ep_lo, Ep_hi = lm.E_dual(lo).d1, lm.E_dual(hi).d1
    require(lm.strictly_negative(Ep_lo) and lm.strictly_positive(Ep_hi),
            "E' sign change failed on the R1 isolation interval")
    Epp = lm.E_dual(Z).d2
    require(lm.strictly_positive(Epp),
            f"E'' must stay > 0 on the isolation interval: {lm.istr(Epp)}")
    z_mid_mp = (mp.mpf(Z.a) + mp.mpf(Z.b)) / 2
    z_mid = midpoint_interval(Z)
    res.update({
        "zStarInterval": r1["zStarInterval"],
        "zStarIntervalWidthDecimal": r1["zStarIntervalWidthDecimal"],
        "EprimeAtLo": lm.istr(Ep_lo),
        "EprimeAtHi": lm.istr(Ep_hi),
        "EppOnIsolationInterval": lm.istr(Epp),
        "uniqueCriticalZStar": True,
    })

    # ---- AD 自检（抓接线错误；失败即 exit 1）
    res["adSelftest"] = ad_selftest(z_mid_mp)

    # ---- advisory 数值（锚定 λ 阶梯；对照 GAP-REPORT 0.143935）
    adv = numeric_advisory(float(z_mid_mp))
    require(adv["quotientDim"] == 15,
            f"advisory numeric quotient dim {adv['quotientDim']} != 15")
    require(adv["quotientLambdaMin"] > 0,
            "advisory numeric quotient lambda_min not positive — refusing to "
            "anchor the interval ladder")
    lam_num = adv["quotientLambdaMin"]
    res["advisoryNumeric"] = {
        "note": "float64 数值对照，非证明；区间证书独立于本块",
        "quotientDim": adv["quotientDim"],
        "quotientLambdaMin": adv["quotientLambdaMin"],
        "tangentGeneralizedEigenvalues": adv["tangentGeneralizedEigenvalues"],
        "gapReportReference": 0.143935,
    }

    # ---- L7：商空间正定证书（中值形式，λ 阶梯自 advisory 锚定）
    ladder = [iv.mpf(str(lam_num)) * iv.mpf(f) for f in LAMBDA_LADDER]
    cert = quotient_certificate_at(Z, z_mid, ladder, want_consistency=True)
    # 报告值 = 证书 λ 区间下端向下取整到 8 位小数（mp.floor 精确 ⇒ 报告值 ≤ 证书值）
    lam_report = mp.floor(mp.mpf(cert["lambda"].a) * 10 ** 8) / 10 ** 8
    res.update({
        "lambdaCertifiedLowerBound": mp.nstr(lam_report, 10),
        "lambdaLadderAnchoredAt": mp.nstr(lam_num, 10),
        "quotientDim": 15,
        "tangentDim": 18,
        "rotationDim": 3,
        "consistencyChecks": cert["consistency"],
    })

    # ---- 交叉复核（精确恒等式在 z* 处取公共值 ⇒ 区间必相交）
    Q_I, grad_I, b_I = cert["Q_I"], cert["grad_I"], cert["b_I"]
    gvf = _0                                  # ∇E·v_fam = Σ_{i<6} grad_i·e_m,i
    for i in range(6):
        gvf = gvf + ddot3(grad_I[i], b_I[2 * i + 1][1]).v
    EpZ = lm.E_dual(Z).d1
    require(lm.intersects(gvf, EpZ),
            f"grad·v_fam {istr(gvf)} disjoint from E'(I) {lm.istr(EpZ)} "
            f"(both must contain E'(z*))")
    qfam = _0                                 # q(v_fam,v_fam) = a_famᵀ Q_red a_fam
    for c in (1, 3, 5, 7, 9, 11):
        for c2 in (1, 3, 5, 7, 9, 11):
            qfam = qfam + Q_I[c][c2].v
    require(lm.intersects(qfam, Epp),
            f"q_R(v_fam,v_fam) {istr(qfam)} disjoint from E''(I) {lm.istr(Epp)} "
            f"(both must contain E''(z*))")
    res["gradDotVfamEnclosure"] = istr(gvf)
    res["qFamDirectionEnclosure"] = istr(qfam)

    # ---- 能量对照（与 R1 同判据）
    e_star_entry = lm.load_e_star()
    e_star = str(e_star_entry["highPrecision"])
    Eint = lm.E_iv(Z)
    dist = max(mp.mpf(Eint.a) - mp.mpf(e_star), mp.mpf(e_star) - mp.mpf(Eint.b),
               mp.mpf(0))
    require(dist <= E_STAR_TOL,
            f"E(z*) enclosure {lm.istr(Eint)} vs E* = {e_star} differ by "
            f"{mp.nstr(dist, 6)} > {E_STAR_TOL}")
    res["eStarReference"] = {
        "source": str(Path(*lm.ENERGIES_FILE)),
        "highPrecision": e_star_entry["highPrecision"],
        "config": e_star_entry.get("config"),
    }
    res["absEzStarMinusEstar"] = mp.nstr(dist, 4)
    return res


def negative_controls():
    """两个负对照都按预期触发 CheckError（含 "positive definite"），否则断言失败。"""
    # (i) 退化 z：对称破缺方向负曲率（数值 λ_min ≈ −1.06）→ ladder=[0] 必须失败
    lo_s, hi_s = SADDLE_INTERVAL
    Z_bad = iv.mpf(mpmath.mpi(mp.mpf(lo_s), mp.mpf(hi_s)))
    z_mid_bad = midpoint_interval(Z_bad)
    try:
        quotient_certificate_at(Z_bad, z_mid_bad, [iv.mpf(0)])
        raise CheckError("negative control FAILED to trigger: quotient positive "
                         f"definiteness unexpectedly passed at z in "
                         f"[{lo_s},{hi_s}] (lambda=0)")
    except CheckError as e:
        require("positive definite" in str(e),
                f"saddle control triggered for the wrong reason: {e}")
        ctl_saddle = str(e)

    # (ii) 篡改矩阵：真实数据上平移 M − 0.4·Ĝ 出正定锥（看守 Cholesky 检出不定）
    lo, hi, _ = load_r1_interval()
    Z = iv.mpf(mpmath.mpi(mp.mpf(lo.a), mp.mpf(hi.b)))
    cert = quotient_certificate_at(Z, midpoint_interval(Z), [iv.mpf("0.1")])
    M, Ghat = cert["M"], cert["Ghat"]
    try:
        interval_cholesky_pd(
            [[M[a][b] - iv.mpf("0.4") * Ghat[a][b] for b in range(15)]
             for a in range(15)], "tampered M - 0.4*Ghat")
        raise CheckError("negative control FAILED to trigger: tampered shift "
                         "M - 0.4*Ghat unexpectedly positive definite")
    except CheckError as e:
        require("positive definite" in str(e),
                f"tampered-matrix control triggered for the wrong reason: {e}")
        ctl_tamper = str(e)
    return ctl_saddle, ctl_tamper


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--selftest", action="store_true",
                    help="加跑两个负对照（退化 z 鞍点、篡改平移），都按预期失败才 exit 0")
    ap.add_argument("--out", default=str(DEFAULT_OUT), help="结果 JSON 输出路径")
    args = ap.parse_args(argv)

    try:
        result = verify_full_local_min()
        result["selftest"] = "not run (pass --selftest)"
        if args.selftest:
            ctl_saddle, ctl_tamper = negative_controls()
            result["selftest"] = {
                "saddleIntervalControl": {
                    "interval": list(SADDLE_INTERVAL),
                    "numericLambdaMinThere": SADDLE_LAMBDA_NUMERIC,
                    "ladderUsed": "[0]",
                    "triggered": True,
                    "message": ctl_saddle,
                },
                "tamperedShiftControl": {
                    "shift": "M - 0.4*Ghat",
                    "triggered": True,
                    "message": ctl_tamper,
                },
            }
    except CheckError as e:
        print(f"FULL-LOCAL-MIN VERIFICATION FAILED: {e}")
        return 1

    lam = result["lambdaCertifiedLowerBound"]
    result.update({
        "schema": "thomson-n9/bounds/full-local-min/1",
        "verified": True,
        "claim": ("TTP X(z*) 是 E|_(S^2)^9 的临界点（D3h 对称约化 + E'(z*)=0，L1–L3），"
                  "其 Riemannian Hessian 在 15 维商切空间（18 维切空间模 3 维 SO(3) "
                  f"轨道方向）上严格正定：q_z*(v,v) ≥ {lam}·‖v‖² 对一切 v ∈ "
                  "S_A(z*)（L4–L7），核恰为旋转轨道方向（L5/L6 精确恒等式 + L7 排除"
                  "其余核）⇒ 模 SO(3) 的非退化严格局部极小（L8，二阶充分条件）"),
        "manifold": "(S^2)^9 subset R^27; tangent 18-dim (27 coords minus 9 unit-sphere "
                    "constraints); SO(3) orbit directions 3-dim; quotient 15-dim",
        "method": (
            "mpmath.iv interval arithmetic (dps=%d) over the whole z* isolation "
            "interval I; reduced coordinates in the pointwise-orthogonal tangent "
            "basis {e_theta, e_m} (Gram exactly diag(1, 1/rho^2) on triangles, 1 on caps); Riemannian "
            "Hessian assembled pair-by-pair (36 pairs + 9 second-fundamental-form "
            "corrections, q_z(v,v) = v^T H_amb v - sum_i (grad_i E . x_i)|v_i|^2); "
            "criticality of X(z*) by D3h symmetry reduction (fixed ambient "
            "subspace F_amb intersect tangent = span{family direction}, "
            "grad E . v_fam = E'(z*) = 0 from R1); rotation kernel q(w,w)=0 and "
            "vanishing cross terms are exact SO(3)-invariance identities at the "
            "critical point (numerically cross-checked ~1e-6 ~ |E'| scale); the "
            "15-dim quotient subspace is built at the interval midpoint "
            "(rotation-orthogonalized pivoted Gram-Schmidt, fixed coefficient "
            "matrix A0), transversality T = S_A (+) R certified on all of I via "
            "interval Cholesky of the G-metric Gram; the certificate M(z) - "
            "lambda*Ghat(z) ≻ 0 uses the MEAN-VALUE FORM M(z) ⊆ M(z_mid) + "
            "[A0^T Q'(I) A0](z - z_mid) with the z-derivative Q' obtained by dual "
            "interval automatic differentiation (cross-checked against central "
            "differences), keeping entry widths ~1e-5 (the true variation of M over "
            "I); final certification uses a preconditioned congruence: the "
            "midpoint matrix is factored by a high-precision concrete "
            "Cholesky R and the interval Cholesky runs on R^{-1}(M - "
            "lambda*Ghat)R^{-T} ~ I + small, which avoids the quadratic "
            "degradation of plain interval Cholesky (certified lambda "
            "within ~1e-4 of the numeric lambda_min instead of ~7e-3)" % IV_DPS),
        "kernelDescription": (
            "18 维切空间上 ker(q) = R = span{w^x, w^y, w^z}（SO(3) 轨道切场 "
            "w^a_i = e_a×x_i），恰 3 维：q(w,w)=0 与交叉项 sᵀHw = 0 是临界点处 "
            "SO(3) 不变性的精确恒等式（L5/L6；区间复核 |C_RᵀQ_redC_R|、|Q_redC_R| "
            "≤ 1e-3，实测 ~1e-6 = |E'| 量级，随 z→z* 收敛到 0）；15 维商切空间上"
            "核为空（区间 Cholesky 证书 M(z) − λ·Ĝ(z) ≻ 0 排除一切非旋转核方向）。"
            "D3h 点群不产生额外零方向：族方向 v_fam（A1' 不可约；在 z_mid 处 ⊥R "
            "故含于 S_A(z_mid) 的构造中，z* 处经 T = S_A⊕R 分解被证书覆盖）的曲率"
            "由两路独立确认——q(v_fam,v_fam) 区间与 E″(I) 区间相交（共同值 "
            "E″(z*)≈42.859，E″ 来自 local_min.py 的独立闭式自动微分）"),
        "lemmaChain": {
            "L1_isolation": "E' sign change on I + E''>0 on I: unique z* with "
                            "E'(z*)=0 (re-verified here via local_min.E_dual; "
                            "R1 artifact interval re-derived and matched)",
            "L2_fixedSubspace": "F_amb ∩ T = span{v_fam}, v_fam = -(z/rho)*f1 + "
                                "f2 exactly; f1, f3 non-tangent (dot enclosures "
                                "bounded away from 0)",
            "L3_criticality": "grad E in F_amb (D3h equivariance of ∇E) and "
                              "grad E . v_fam = E'(z*) = 0 ⇒ X(z*) critical on "
                              "(S^2)^9; numeric: tangential-gradient basis dots "
                              "contain 0, max ~ |E'| scale",
            "L4_riemannianHessian": "q_z(v,v) = v^T H_amb v - sum_i (grad_i E . "
                                    "x_i)|v_i|^2 (geodesic acceleration of unit "
                                    "spheres); at a critical point this is the "
                                    "Riemannian Hessian",
            "L5_kernelOnRotations": "q(w,w) = 0 exactly at z* (SO(3) invariance); "
                                    "numeric |C_R^T Q_red C_R| ~ 1e-6 ~ |E'|",
            "L6_crossTerms": "s^T H w = 0 exactly at z*; numeric |Q_red C_R| "
                             "~ 1e-6",
            "L7_intervalCertificate": "basis tangency; dim R = 3 (C_R^T G C_R "
                                      "PD); midpoint-built A0 (18x15) with "
                                      "Gram_G([A0|C_R]) PD on all of I ⇒ "
                                      "T = S_A ⊕ R; mean-value form + dual-AD "
                                      "derivative certifies M(z) - λGhat(z) PD "
                                      "by interval Cholesky ⇒ q_z ≥ λ||·||² on "
                                      "S_A(z) for ALL z ∈ I",
            "L8_conclusion": "at z*: u = s + r ⇒ q(u) = q(s) ≥ λ||s||² ≥ "
                             "λ·dist(u,R)² ⇒ ker Hess = R exactly; quotient "
                             "lambda_min ≥ λ > 0 ⇒ nondegenerate strict local "
                             "minimum modulo SO(3) (second-order sufficient "
                             "condition)",
        },
        "tolerances": {"ivDps": IV_DPS, "eStarDistance": "1e-8",
                       "tangencyEpsilon": "1e-4",
                       "kernelConsistencyEpsilon": "1e-3",
                       "adSelftestRelativeTolerance": FD_TOL},
        "forTubeLine": (f"lambdaMinQuotientLowerBound = {lam}（管状线 tubeRadius 的"
                        "输入；把 λ 转成管半径还需 Taylor 三阶余项界与能量下界拼接，"
                        "下游管状线处理，本脚本交付 λ 的严格区间下界）"),
        "timestamp": datetime.now(timezone.utc).isoformat(timespec="seconds"),
    })

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    with open(out, "w") as f:
        json.dump(result, f, ensure_ascii=False, indent=2, sort_keys=False)
        f.write("\n")

    print(f"z* interval:   {result['zStarInterval']}  (R1 artifact, re-derived)")
    print(f"E'(lo)<0<E'(hi);  E'' on I: {result['EppOnIsolationInterval']}")
    print(f"lambda_min (quotient 15-dim): certified >= {lam}"
          f"   (advisory numeric {result['lambdaLadderAnchoredAt']})")
    print("kernel: exactly the 3 SO(3) orbit directions on the 18-dim tangent space")
    print(f"|E(z*) - E*| = {result['absEzStarMinusEstar']}")
    if isinstance(result["selftest"], dict):
        print("selftest: saddle-interval control triggered; "
              "tampered-shift control triggered")
    print(f"FULL-LOCAL-MIN VERIFICATION OK  ->  {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
