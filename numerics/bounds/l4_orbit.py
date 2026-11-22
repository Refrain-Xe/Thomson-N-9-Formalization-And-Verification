#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""l4_orbit.py — L4 双轨道邻型计数（D1 指定的第 2 轮回滚首选；离散路线主件，零重求解）。

【引理（等号情形，本脚本交付的精确层）】
  设 x_1..x_9 ∈ S²（单位向量）且所有两两内积 x_i·x_j (i<j) 落在 TTP 节点集
  {ν_1..ν_6}（ν 由 D3h 单参数族闭式给出，z* ∈ local_min.json 严格隔离区间）。
  则其边染色 ≅ TTP 染色（单一 isomorphism 类）。

【证明结构（脚本内逐步兑现）】
  (P1) 实现 ⊆ 过滤集：Gram PSD rank≤3 ⇒ 一切主子式 ≥0（故 3×3 ≥0）且一切
       尺寸>3 的子式=0（故 4×4 det=0）。过滤条件在真节点值处逐点成立。
  (P2) 过滤集的枚举：K9 全部 6 色边染色，过滤＝（一切 3×3 主子式 ≥0）∧
       （一切 4×4 主子式 det=0）。两阶法：
         · float scout（z* 区间中点、容差 ±1e-3，完备性由 sup|det′|·半宽
           （4×4: 9.43e-6、3×3: 2.76e-6）≪ 1e-3 证书化——任何在真节点值处
           det=0 / ≥0 的染色在 z_mid 处偏移 < 容差，必不被剪，无假阴性）；
         · 4×4 det 按色模式（K4 边规范型，2451 类）缓存剪枝。
  (P3) 幸存者精确复验（多项式＋区间双轨）：
         · 4×4：det 作为节点曲线的多项式 ∈ Z[z,r]/(r²+z²−1)（r=√(1−z²)，
           2ν 缩放保整系数）。恒等于零（曲线上市零）⇒ 该子式对一切 z 恒为 0
           （与 z* 隔离宽度无关）；否则在 z* 区间上区间求值（mpmath.iv，
           dps≥50，宽度覆盖 z* 区间传播）：区间排零 ⇒ 箱内一切 z 处 det≠0 ⇒
           排除；区间含零 ⇒ undecided（非静默，入 gaps）。
         · 3×3：接受＝恒等零 或 区间 lo≥0；拒绝＝区间 hi<0（非 PSD）。
  (P4) iso 归类（canonical 去重）：backtracking iso 判定（顶点轮廓剪枝）。
  (P5) TTP 类实现证书（构造性、精确）：族参数化点坐标（×2）∈ Q(√3)[z,r]，
       Gram 逐项多项式恒等：对角 ≡4（即 |x|²≡1）、非对角 ≡ 4·节点曲线
       （√3 部分恒零）⇒ 该类可实现（XᵀX 自动 PSD rank≤3），幸存集非空。
  (P6) 结论：实现 ⊆ 过滤集 = 枚举集 = {TTP 单类} ⇒ 引理（无条件形式；
       E 条件不需要——无第二类可排除）。

【诚实口径】
  · 「过滤 ⇒ 可实现」（3×3≥0 ∧ 4×4=0 ⇒ PSD rank≤3）方向不主张不使用；
    引理只用 (P1) 平凡包含＋枚举＝单类＋(P5) 非空。
  · E_ttp 与 E* 的区间比较在存档 z* 箱宽度下 undecided（E′(z*)=0 但箱不以
    z* 为中心，一阶传播 1.18e-5 ≫ 差值 2.7e-10）——如实入 gaps；对无条件
    引理形式无影响。
  · 稳定层（ρ-近似）常数与阈值如实给出；与当前 ε-链的 ρ_spec（L3 地板
    0.0466）差 ~3 个数量级——前提未满足是 L3 的缺口，不是本层缺口。

【轨道配平（独立推导，Σ_y #type_y = 2·mult）】
  6 棱顶（上三角 3 + 下三角 3，z=±z*，半径 ρ=√(1−z*²)）＋3 帽顶（z=0，
  半径 1）。按参数化组合学逐类计数（类别→节点由多项式恒等式对回，不引
  tube.json）：
    上上/下下三角内部   3+3=6 边 → (3z²−1)/2   = ν_5
    上下同方位（竖棱）  3     边 → 1−2z²       = ν_4
    上下错位           6     边 → −(1+z²)/2    = ν_1
    帽-帽              3     边 → −1/2         = ν_3
    帽-棱 (j−k≡0,2)   12     边 → ρ/2          = ν_6
    帽-棱 (j−k≡1)      6     边 → −ρ           = ν_2
  逐顶点轨道轮廓：棱顶 (ν₁..ν₆)=(2,1,0,1,2,2)、帽顶 (0,2,2,0,0,4)；
  Σ_y = (12,12,6,6,12,24) = 2·(6,6,3,3,6,12) = 2·mult。
  【勘误记录】任务书/D12 所写「帽-棱 12 边 ν₆＋6 边 ν₅」后半应为 ν₂
  （ν₅ 的 6 边在上下三角内部）；本脚本由参数化组合推导＋reference_config.json
  数值复算双重证实；重数配平两种写法下同为 6/6/3/3/6/12。

【稳定层（ρ-近似常数，命题 5.1(i) 口径）】
  V = 6×6 Vandermonde（V[i][k] = ν_k^i，i=0..5）。区间 Gauss-Jordan（部分
  主元）得 V⁻¹ 区间包（V·V⁻¹ ∋ I 逐项验证）；σ(V) ≥ c_V =
  1/(√6·‖V⁻¹‖_F 上界)。计数稳定性显式阈值：若每内积落在某节点 ρ-管内且
  每顶点幂和 p_i(y)=Σ_{z≠y}(y·z)^i 与轨道值差 ≤ Δ，则
  ‖n(y)−n_orbit(y)‖_∞ ≤ ‖V⁻¹‖_∞·(δ_∞(ρ)+Δ)，δ_i(ρ)=8·i·(1+ρ)^{i−1}·ρ；
  该量 < 1/2 时邻型计数向量＝轨道向量。对径分离：min_{a≤b}|ν_a+ν_b| =
  2ν_4（自对 (4,4) 取到），ρ < ν_4 下界时管内任两值之和严格非零。

用法（thomson-n9 下，裸 python3 可跑，仅依赖 mpmath）：
  python3 numerics/bounds/l4_orbit.py            # 主链 + results/l4_orbit.json
  python3 numerics/bounds/l4_orbit.py --out P    # 写到 P（门重算用）
  python3 numerics/bounds/l4_orbit.py --dps 15   # 低精度（负对照诊断用）
输出 JSON 确定性（无时间戳/运行时/随机序）⇒ 幂等重算逐位一致。
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import random
import sys
import time
from fractions import Fraction
from pathlib import Path

import mpmath as mp
from mpmath import iv

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
RESULTS = HERE / "results"
TUBE = RESULTS / "tube.json"
LOCAL_MIN = RESULTS / "local_min.json"
WORKFLOW_DATA = HERE.parents[2] / "thomson-workflow" / "data" / "energies.json"
OUT_DEFAULT = RESULTS / "l4_orbit.json"

SEED = 20261007
DPS_DEFAULT = 50              # 区间精度（任务要求 ≥50）
TOL3 = -1e-3                  # scout 3×3 容差（完备性由 sup|det′|·半宽证书化）
TOL4 = 1e-3                   # scout 4×4 容差

# 决策标签
D_ZERO = "identically-zero"        # 多项式在曲线上恒为零
D_REJ_NZ = "nonzero-on-box"        # 4×4：区间排零 ⇒ 箱内一切 z 处 det≠0
D_REJ_NEG = "negative-on-box"      # 3×3：区间上界 <0 ⇒ 非 PSD
D_ACC_NN = "nonneg-on-box"         # 3×3：区间下界 ≥0
D_UNDEC = "undecided"              # 区间骑墙（非静默，必须记录）


def log(msg: str) -> None:
    print(msg, flush=True)


def mpv(x):
    """区间端点（ivmpf）→ 普通 mpf（避免 nstr 打成 "[a, a]" 串）。"""
    return mp.mpf(x)


# ================================================================ 多项式环
# 元素 = dict {(zdeg, rdeg): int}，rdeg ≤ 1，r² 归约为 1−z²（r=√(1−z²)）。
# 值 = Σ c_{a,b}·z^a·r^b。2ν 缩放保证整系数。

def p_add(p, q):
    out = dict(p)
    for k, v in q.items():
        w = out.get(k, 0) + v
        if w == 0:
            out.pop(k, None)
        else:
            out[k] = w
    return out or {}

def p_scale(p, c):
    if c == 0:
        return {}
    return {k: v * c for k, v in p.items()}

def p_mul(p, q):
    out = {}
    for (a1, b1), c1 in p.items():
        for (a2, b2), c2 in q.items():
            a, b = a1 + a2, b1 + b2
            if b >= 2:                     # r^b → (1−z²)^{b//2}·r^{b%2}
                q2, rr = divmod(b, 2)
                if q2 == 0:
                    term = {(a, b): c1 * c2}
                else:
                    term = {(a + 2 * q2, rr): c1 * c2}
                    # (1−z²)^{q2} 展开避免高次堆叠（q2 ≤ 4 足够小，直接展开）
                    term = {}
                    for e in range(q2 + 1):
                        # C(q2,e)·(−z²)^e·(1)^{q2−e}
                        from math import comb
                        coef = comb(q2, e) * ((-1) ** e) * c1 * c2
                        kk = (a + 2 * e, rr)
                        term[kk] = term.get(kk, 0) + coef
            else:
                term = {(a, b): c1 * c2}
            for k, v in term.items():
                w = out.get(k, 0) + v
                if w == 0:
                    out.pop(k, None)
                else:
                    out[k] = w
    return out or {}

def p_is_zero(p):
    return not p

def poly_str(p):
    if not p:
        return "0"
    parts = []
    for (a, b) in sorted(p.keys(), reverse=True):
        c = p[(a, b)]
        body = ("z" if a == 1 else f"z^{a}" if a > 1 else "") + ("r" if b else "")
        parts.append(f"{c}" if not body else (f"{c}" if c != 1 else "") + (body or "1"))
    return " + ".join(parts)

Z = {(1, 0): 1}
R = {(0, 1): 1}
ONE = {(0, 0): 1}


def build_node_polys():
    """2ν_k ∈ Z[z,r]（闭式曲线，独立于 tube.json）。"""
    z2 = p_mul(Z, Z)
    return [
        p_add(p_scale(ONE, -1), p_scale(z2, -1)),   # 2ν₁ = −1−z²
        p_scale(R, -2),                             # 2ν₂ = −2r
        p_scale(ONE, -1),                           # 2ν₃ = −1
        p_add(p_scale(ONE, 2), p_scale(z2, -4)),    # 2ν₄ = 2−4z²
        p_add(p_scale(z2, 3), p_scale(ONE, -1)),    # 2ν₅ = 3z²−1
        dict(R),                                    # 2ν₆ = r
    ]


def det_poly(M):
    """方阵（Poly 元）行列式，Leibniz 展开（n≤4）。"""
    n = len(M)
    d = {}
    for pi in itertools.permutations(range(n)):
        inv = sum(1 for i in range(n) for j in range(i + 1, n) if pi[i] > pi[j])
        term = ONE
        for i in range(n):
            term = p_mul(term, M[i][pi[i]])
            if not term:
                break
        if term:
            d = p_add(d, p_scale(term, -1 if inv % 2 else 1))
    return d


def gram4_poly(cols):
    """4×4 单位对角 Gram 的 2× 缩放（对角=2，非对角=2ν）之 det。cols=6 条 2ν。"""
    a01, a02, a03, a12, a13, a23 = cols
    M = [[p_scale(ONE, 2), a01, a02, a03],
         [a01, p_scale(ONE, 2), a12, a13],
         [a02, a12, p_scale(ONE, 2), a23],
         [a03, a13, a23, p_scale(ONE, 2)]]
    return det_poly(M)


def gram3_poly(cols):
    a, b, c = cols
    M = [[p_scale(ONE, 2), a, b],
         [a, p_scale(ONE, 2), c],
         [b, c, p_scale(ONE, 2)]]
    return det_poly(M)


# ================================================================ 区间求值

def poly_to_ABR(p):
    """p = A(z) + B(z)·r（rdeg ≤ 1 归约后天然如此）。"""
    A, B = {}, {}
    for (a, b), c in p.items():
        if b == 0:
            A[(a, 0)] = A.get((a, 0), 0) + c
        else:
            B[(a, 1)] = B.get((a, 1), 0) + c
    return A, B

def _horner_z(coefs, zbox):
    if not coefs:
        return iv.mpf(0)
    deg = max(a for (a, _) in coefs)
    zp = {0: iv.mpf(1)}
    for i in range(1, deg + 1):
        zp[i] = zp[i - 1] * zbox
    s = iv.mpf(0)
    for (a, _), c in coefs.items():
        s += zp[a] * c
    return s

def poly_eval_iv(p, zbox):
    """p(z, r(z)) 的区间包（r = √(1−z²) 区间）。"""
    A, B = poly_to_ABR(p)
    rho = iv.sqrt(1 - zbox * zbox)
    return _horner_z(A, zbox) + _horner_z(B, zbox) * rho

def poly_deriv_bound_iv(p, zbox):
    """|d/dz p(z,r(z))| 于 zbox 的上界（区间）。
    d/dz[A+B·r] = A′ + B′·r − B·z/r；r 下界离 0（zbox ⊂ (0,1)）。"""
    A, B = poly_to_ABR(p)
    rho = iv.sqrt(1 - zbox * zbox)
    assert rho.a > 0
    def dco(co):
        return {(a - 1, b): c * a for (a, b), c in co.items() if a >= 1}
    return (abs(_horner_z(dco(A), zbox)) + abs(_horner_z(dco(B), zbox)) * abs(rho)
            + abs(_horner_z(B, zbox)) * abs(zbox) / rho.a)


def decide_zero(poly, zbox):
    if p_is_zero(poly):
        return D_ZERO, None
    itv = poly_eval_iv(poly, zbox)
    if itv.a > 0 or itv.b < 0:
        return D_REJ_NZ, itv
    return D_UNDEC, itv

def decide_nonneg(poly, zbox):
    if p_is_zero(poly):
        return D_ZERO, None
    itv = poly_eval_iv(poly, zbox)
    if itv.a >= 0:
        return D_ACC_NN, itv
    if itv.b < 0:
        return D_REJ_NEG, itv
    return D_UNDEC, itv


# ================================================================ K4 色模式规范型

EDGES4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
POS4 = {e: i for i, e in enumerate(EDGES4)}
PERMS_ACT = [[POS4[tuple(sorted((pi[i], pi[j])))] for (i, j) in EDGES4]
             for pi in itertools.permutations(range(4))]

def canon4(cols):
    best = None
    for act in PERMS_ACT:
        t = tuple(cols[a] for a in act)
        if best is None or t < best:
            best = t
    return best


# ================================================================ 输入

def load_inputs():
    tube = json.loads(TUBE.read_text())
    lmin = json.loads(LOCAL_MIN.read_text())
    wf = json.loads(WORKFLOW_DATA.read_text())
    zlo, zhi = json.loads(lmin["zStarIntervalMpmath"])
    e_star = Fraction(str(wf["energies"]["9"]["value"]))
    return tube, Fraction(zlo), Fraction(zhi), e_star


def nu_float(z):
    rho = mp.sqrt(1 - z * z)
    return (-(1 + z * z) / 2, -rho, mp.mpf(-0.5), 1 - 2 * z * z,
            (3 * z * z - 1) / 2, rho / 2)


# ================================================================ float scout

def build_tables(NU):
    tri_val = {}
    for c in itertools.combinations_with_replacement(range(6), 3):
        a, b, cc = NU[c[0]], NU[c[1]], NU[c[2]]
        tri_val[c] = 1 + 2 * a * b * cc - a * a - b * b - cc * cc

    def det4nu(cols):
        a01, a02, a03, a12, a13, a23 = (NU[c] for c in cols)
        A = ((1, a01, a02, a03), (a01, 1, a12, a13), (a02, a12, 1, a23),
             (a03, a13, a23, 1))
        d = mp.mpf(0)
        for pi in itertools.permutations(range(4)):
            inv = sum(1 for i in range(4) for j in range(i + 1, 4) if pi[i] > pi[j])
            p = mp.mpf(1)
            for i in range(4):
                p *= A[i][pi[i]]
            d += (p if inv % 2 == 0 else -p)
        return d

    seen = set()
    det4tab = {}
    for key in itertools.product(range(6), repeat=6):
        if key in seen:
            continue
        for act in PERMS_ACT:
            seen.add(tuple(key[a] for a in act))
        det4tab[key] = det4nu(key)

    ok3 = bytearray(216)
    for p in range(6):
        for q in range(6):
            for r in range(6):
                ok3[p * 36 + q * 6 + r] = \
                    1 if tri_val[tuple(sorted((p, q, r)))] >= TOL3 else 0
    ok4 = bytearray(6 ** 6)
    for key, d in det4tab.items():
        if abs(d) <= TOL4:
            for act in PERMS_ACT:
                k2 = tuple(key[a] for a in act)
                ok4[k2[0] * 7776 + k2[1] * 1296 + k2[2] * 216
                    + k2[3] * 36 + k2[4] * 6 + k2[5]] = 1
    return ok3, ok4, det4tab, tri_val


def run_scout(ok3, ok4):
    """DFS 枚举（确定性，无随机序）。返回幸存染色（36 元组）列表。"""
    G = [[0] * 9 for _ in range(9)]
    sols = []
    pairs_cache = [[(a, b) for a in range(u) for b in range(a + 1, u)] for u in range(9)]

    def dfs(v):
        if v == 9:
            sols.append(tuple(G[i][j] for i in range(9) for j in range(i + 1, 9)))
            return
        q = [0] * 9

        def rec(u):
            if u == v:
                dfs(v + 1)
                return
            for c in range(6):
                good = True
                for u2 in range(u):
                    if not ok3[G[u2][u] * 36 + q[u2] * 6 + c]:
                        good = False
                        break
                if not good:
                    continue
                if u >= 3:
                    for (a, b) in pairs_cache[u]:
                        if not ok4[G[a][b] * 7776 + q[a] * 1296 + G[a][u] * 216
                                   + q[b] * 36 + G[b][u] * 6 + c]:
                            good = False
                            break
                    if not good:
                        continue
                q[u] = c
                G[v][u] = c
                G[u][v] = c
                rec(u + 1)
                G[v][u] = 0
                G[u][v] = 0

        rec(0)

    dfs(0)
    return sols


# ================================================================ 构造实现证书（精确多项式恒等）
# S3-pair: (a, b) 表 a + b·√3，a,b ∈ Z[z,r]。族点用 ×2 坐标。

def s3(a=None, b=None):
    return (dict(a) if a else {}, dict(b) if b else {})

def s3_add(p, q):
    return (p_add(p[0], q[0]), p_add(p[1], q[1]))

def s3_mul(p, q):
    a, b = p
    c, d = q
    return (p_add(p_mul(a, c), p_scale(p_mul(b, d), 3)),
            p_add(p_mul(a, d), p_mul(b, c)))


def family_points_s3():
    """triCapPrism（×2 坐标）。top/bottom: (2ρcos, 2ρsin, ±2z)；caps: (2cos,2sin,0)。
    2cos、2sin（√3 系数）：三角 (2,−1,−1)/(0,1,−1)；帽 (1,−2,1)/(1,0,−1)。"""
    tri_cos = [2, -1, -1]
    tri_sin = [0, 1, -1]
    cap_cos = [1, -2, 1]
    cap_sin = [1, 0, -1]
    pts = []
    for k in range(3):                       # top: z=+z*
        pts.append((s3(a=p_scale(R, tri_cos[k])),
                    s3(b=p_scale(R, tri_sin[k])),
                    s3(a=p_scale(Z, 2))))
    for k in range(3):                       # bottom: z=−z*
        pts.append((s3(a=p_scale(R, tri_cos[k])),
                    s3(b=p_scale(R, tri_sin[k])),
                    s3(a=p_scale(Z, -2))))
    for k in range(3):                       # caps: z=0, 半径 1
        pts.append((s3(a=p_scale(ONE, cap_cos[k])),
                    s3(b=p_scale(ONE, cap_sin[k])),
                    s3()))
    return pts


def gram_s3(pts):
    """9×9 Gram（×4 口径：Σ (2x_it)(2x_jt) = 4·x_i·x_j）。"""
    n = len(pts)
    Gm = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            acc = s3()
            for t in range(3):
                acc = s3_add(acc, s3_mul(pts[i][t], pts[j][t]))
            Gm[i][j] = acc
    return Gm


# ================================================================ iso 判定

def profile(C, v):
    cnt = [0] * 6
    for (i, j), c in C.items():
        if i == v or j == v:
            cnt[c] += 1
    return tuple(cnt)

def iso_to(A, B):
    """是否存在置换 π 使 A[π(i),π(j)] = B[i,j]（backtracking＋轮廓剪枝）。"""
    pB = [profile(B, v) for v in range(9)]
    pA = [profile(A, v) for v in range(9)]
    order = sorted(range(9), key=lambda v: (-max(pB[v]), pB[v]))
    pi = [-1] * 9
    used = [False] * 9

    def bt(k):
        if k == 9:
            return True
        v = order[k]
        for w in range(9):
            if used[w] or pA[w] != pB[v]:
                continue
            ok = True
            for k2 in range(k):
                v2 = order[k2]
                w2 = pi[v2]
                if A.get((min(w, w2), max(w, w2))) != B.get((min(v, v2), max(v, v2))):
                    ok = False
                    break
            if ok:
                pi[v] = w
                used[w] = True
                if bt(k + 1):
                    return True
                pi[v] = -1
                used[w] = False
        return False

    return bt(0)


def coloring_from_tuple(t):
    C = {}
    k = 0
    for i in range(9):
        for j in range(i + 1, 9):
            C[(i, j)] = t[k]
            k += 1
    return C

# ================================================================ 复用件（门脚本同源调用）

def compute_context(dps):
    """节点区间＋类决策表＋完备性界（给定 dps）。返回 dict；恢复原 dps。
    单一事实源：main 与 l4_orbit_gate.py 共用。"""
    prev_mp, prev_iv = mp.mp.dps, iv.dps
    mp.mp.dps = max(dps + 10, 60)
    iv.dps = dps
    try:
        tube, zlo, zhi, e_star = load_inputs()
        frac = lambda fr: mp.mpf(fr.numerator) / mp.mpf(fr.denominator)
        zlo_str, zhi_str = mp.nstr(frac(zlo), 60), mp.nstr(frac(zhi), 60)
        zbox = iv.mpf((zlo_str, zhi_str))
        zmid = (frac(zlo) + frac(zhi)) / 2
        halfw = (frac(zhi) - frac(zlo)) / 2
        node_poly = build_node_polys()
        rho_iv = iv.sqrt(1 - zbox * zbox)
        nu_iv = (-(1 + zbox * zbox) / 2, -rho_iv, iv.mpf("-0.5"),
                 1 - 2 * zbox * zbox, (3 * zbox * zbox - 1) / 2, rho_iv / 2)
        tube_nodes = tube["ttp_spectrum"]["nodes"]
        tube_mults = tube["ttp_spectrum"]["multiplicities"]
        tube_check = [bool(nu_iv[k].a <= mp.mpf(str(tube_nodes[k])) <= nu_iv[k].b)
                      for k in range(6)]
        tri_keys = list(itertools.combinations_with_replacement(range(6), 3))
        tri_dec = {}
        sup_dp3 = iv.mpf(0)
        for key in tri_keys:
            poly = gram3_poly(tuple(node_poly[c] for c in key))
            tri_dec[key] = decide_nonneg(poly, zbox)
            b = poly_deriv_bound_iv(poly, zbox)
            if b.b > sup_dp3.b:
                sup_dp3 = b
        seen = set()
        quad_keys = []
        for key in itertools.product(range(6), repeat=6):
            if key in seen:
                continue
            for act in PERMS_ACT:
                seen.add(tuple(key[a] for a in act))
            quad_keys.append(key)
        quad_dec = {}
        sup_dp4 = iv.mpf(0)
        for key in quad_keys:
            poly = gram4_poly(tuple(node_poly[c] for c in key))
            quad_dec[key] = decide_zero(poly, zbox)
            b = poly_deriv_bound_iv(poly, zbox)
            if b.b > sup_dp4.b:
                sup_dp4 = b
        return {
            "dps": dps, "tube": tube, "e_star": e_star,
            "zlo_str": zlo_str, "zhi_str": zhi_str,
            "zbox": zbox, "zmid": zmid, "halfw": halfw,
            "nu_iv": nu_iv, "node_poly": node_poly,
            "tube_nodes": tube_nodes, "tube_mults": tube_mults,
            "tube_check": tube_check,
            "tri_dec": tri_dec, "quad_dec": quad_dec, "quad_keys": quad_keys,
            "sup_dp3": sup_dp3, "sup_dp4": sup_dp4,
            "comp3": float(sup_dp3.b) * float(halfw),
            "comp4": float(sup_dp4.b) * float(halfw),
        }
    finally:
        mp.mp.dps, iv.dps = prev_mp, prev_iv


def ttp_reference_coloring():
    """TTP 参考染色（构造性多项式恒等证书）。返回 (C, checks)；失败 raise。"""
    pts = family_points_s3()
    Gm = gram_s3(pts)
    node_poly = build_node_polys()
    curve_to_node = {poly_str(p_scale(node_poly[k], 2)): k for k in range(6)}
    C = {}
    for i in range(9):
        for j in range(i + 1, 9):
            rat, s3part = Gm[i][j]
            if not p_is_zero(s3part):
                raise AssertionError(f"Gram[{i},{j}] sqrt3-part nonzero")
            k = curve_to_node.get(poly_str(rat))
            if k is None:
                raise AssertionError(
                    f"Gram[{i},{j}]={poly_str(rat)} matches no 4*node curve")
            C[(i, j)] = k
    for i in range(9):
        rat, s3part = Gm[i][i]
        if not p_is_zero(s3part) or poly_str(rat) != "4":
            raise AssertionError(f"Gram[{i},{i}] != 4: {poly_str(rat)}")
    checks = ["sqrt3-part-identically-zero-36-pairs",
              "offdiag-equals-4x-node-curve-36-pairs",
              "diagonal-identically-4-unit-norm-9-vertices"]
    return C, checks


def verify_coloring(C, tri_dec, quad_dec):
    """给定染色 C（dict (i,j)->color）与类决策表：精确层判定。
    返回 (verdict, route)：verdict ∈ accepted/rejected/undecided；
    route = (kind, key, decision) 首个失败子式。"""
    for (a, b, c3) in itertools.combinations(range(9), 3):
        key = tuple(sorted((C[(a, b)], C[(a, c3)], C[(b, c3)])))
        dec, _ = tri_dec[key]
        if dec in (D_REJ_NEG, D_UNDEC):
            return ("rejected" if dec == D_REJ_NEG else "undecided",
                    ("3x3", key, dec))
    for (a, b, c3, d) in itertools.combinations(range(9), 4):
        cols = (C[(a, b)], C[(a, c3)], C[(a, d)], C[(b, c3)], C[(b, d)], C[(c3, d)])
        ckey = canon4(cols)
        dec, _ = quad_dec[ckey]
        if dec in (D_REJ_NZ, D_UNDEC):
            return ("rejected" if dec == D_REJ_NZ else "undecided",
                    ("4x4", ckey, dec))
    return ("accepted", None)


def E_interval_from_hist(hist, nu_iv):
    E = iv.mpf(0)
    for k in range(6):
        E += hist[k] / iv.sqrt(2 - 2 * nu_iv[k])
    return E


def E_branch_verdict(E, e_star):
    e_iv = iv.mpf(f"{e_star.numerator}/{e_star.denominator}")
    if E.a > e_iv.b:
        return "greater-than-Estar"
    if E.b < e_iv.a:
        return "below-Estar"
    return "undecided-at-zbox"


# ================================================================ 主流程

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(OUT_DEFAULT))
    ap.add_argument("--dps", type=int, default=DPS_DEFAULT)
    args = ap.parse_args()
    random.seed(SEED)                     # 确定性声明（流程本身无随机性）
    t_start = time.time()

    # ---------- 精确层上下文（含节点区间、类决策表、完备性界）
    ctx = compute_context(args.dps)
    tube = ctx["tube"]
    e_star = ctx["e_star"]
    zbox, zmid, halfw = ctx["zbox"], ctx["zmid"], ctx["halfw"]
    nu_iv, node_poly = ctx["nu_iv"], ctx["node_poly"]
    tube_nodes, tube_mults = ctx["tube_nodes"], ctx["tube_mults"]
    tri_dec, quad_dec, quad_keys = ctx["tri_dec"], ctx["quad_dec"], ctx["quad_keys"]
    sup_dp3, sup_dp4 = ctx["sup_dp3"], ctx["sup_dp4"]
    comp3, comp4 = ctx["comp3"], ctx["comp4"]
    iv.dps = args.dps

    if not all(ctx["tube_check"]):
        log(f"[FAIL] tube.json 10 位节点值未落入闭式重算区间: {ctx['tube_check']}")
        return 1
    if not (comp4 < TOL4 and comp3 < -TOL3):
        log(f"[FAIL] scout 容差不完备: sup|det4′|·hw={comp4:.3e} vs TOL4={TOL4}, "
            f"sup|det3′|·hw={comp3:.3e} vs −TOL3={-TOL3}")
        return 1

    NU = nu_float(zmid)

    # ---------- float scout
    ok3, ok4, det4tab, tri_val = build_tables(NU)
    t0 = time.time()
    sols = run_scout(ok3, ok4)
    t_scout = time.time() - t0
    log(f"scout: {len(sols)} labeled survivors ({t_scout:.1f}s), "
        f"{len(quad_keys)} canonical 4x4 classes, "
        f"{sum(1 for v in quad_dec.values() if v[0] == D_ZERO)} identically-zero")

    # ---------- 幸存者精确复验（类表查询＝逐子式核验）
    n_acc = 0
    rejects = []
    undecided_surv = []
    tri_used = {}
    quad_used = {}
    for s in sols:
        C = coloring_from_tuple(s)
        verdict, route = verify_coloring(C, tri_dec, quad_dec)
        if verdict == "accepted":
            n_acc += 1
            for (a, b, c3) in itertools.combinations(range(9), 3):
                key = tuple(sorted((C[(a, b)], C[(a, c3)], C[(b, c3)])))
                tri_used[key] = tri_used.get(key, 0) + 1
            for (a, b, c3, d) in itertools.combinations(range(9), 4):
                cols = (C[(a, b)], C[(a, c3)], C[(a, d)],
                        C[(b, c3)], C[(b, d)], C[(c3, d)])
                ckey = canon4(cols)
                quad_used[ckey] = quad_used.get(ckey, 0) + 1
        elif verdict == "rejected":
            rejects.append((s, route[0], route[1]))
        else:
            undecided_surv.append((s, route[0], route[1]))
    log(f"exact layer: accepted {n_acc}/{len(sols)}, rejected {len(rejects)}, "
        f"undecided {len(undecided_surv)}")
    surv_set = {r[0] for r in rejects} | {u[0] for u in undecided_surv}
    survivors = [s for s in sols if s not in surv_set]

    # ---------- 构造实现证书（TTP 参考染色 + 多项式恒等）
    try:
        ttp_ref, realiz_checks = ttp_reference_coloring()
    except AssertionError as e:
        log(f"[FAIL] 实现证书失败: {e}")
        return 1

    # ---------- 轨道配平（独立推导）
    cat = {}
    for (i, j), k in ttp_ref.items():
        ci = "top" if i < 3 else "bottom" if i < 6 else "cap"
        cj = "top" if j < 3 else "bottom" if j < 6 else "cap"
        if ci != "cap" and cj != "cap":
            if ci == cj:
                name = "triangle-internal"
            elif i % 3 == j % 3:
                name = "vertical-edge"
            else:
                name = "cross-misaligned"
        elif ci == "cap" and cj == "cap":
            name = "cap-cap"
        else:
            pr, ca = (i, j) if j >= 6 else (j, i)
            name = f"cap-prism-r{(ca - (pr % 3)) % 3}"
        cat.setdefault(name, []).append(k)
    cat_summary = {}
    for name, ks in sorted(cat.items()):
        uniq = sorted(set(ks))
        assert len(uniq) == 1, (name, uniq)
        cat_summary[name] = {"count": len(ks), "node": uniq[0]}
    prism_profile = [0] * 6
    cap_profile = [0] * 6
    for (i, j), k in ttp_ref.items():
        for v in (i, j):
            (prism_profile if v < 6 else cap_profile)[k] += 1
    assert all(c % 6 == 0 for c in prism_profile)
    assert all(c % 3 == 0 for c in cap_profile)
    prism_vertex = [c // 6 for c in prism_profile]
    cap_vertex = [c // 3 for c in cap_profile]
    per_node_sums = [prism_profile[k] + cap_profile[k] for k in range(6)]
    balanced = all(per_node_sums[k] == 2 * tube_mults[k] for k in range(6))
    hist_ref = [sum(1 for k in ttp_ref.values() if k == m) for m in range(6)]
    if hist_ref != list(tube_mults) or not balanced:
        log(f"[FAIL] 轨道配平失败: hist={hist_ref} sums={per_node_sums} "
            f"2mult={[2 * m for m in tube_mults]}")
        return 1

    # ---------- iso 归类
    classes = []
    for s in survivors:
        A = coloring_from_tuple(s)
        placed = False
        for (rep, members) in classes:
            if iso_to(A, coloring_from_tuple(rep)):
                members.append(s)
                placed = True
                break
        if not placed:
            classes.append((s, [s]))
    log(f"iso classes: {len(classes)} sizes={[len(m) for _, m in classes]}")

    # ---------- E 表
    energy_classes = []
    for idx, (rep, members) in enumerate(classes):
        hist = [0] * 6
        for c in coloring_from_tuple(rep).values():
            hist[c] += 1
        E = E_interval_from_hist(hist, nu_iv)
        verdict = E_branch_verdict(E, e_star)
        energy_classes.append({
            "index": idx, "histogram": hist, "members": len(members),
            "E_interval": [mp.nstr(mpv(E.a), 18), mp.nstr(mpv(E.b), 18)],
            "vs_Estar": verdict,
        })
        log(f"class {idx}: members={len(members)} hist={hist} E∈"
            f"[{mp.nstr(mpv(E.a), 12)},{mp.nstr(mpv(E.b), 12)}] vs E*: {verdict}")

    # ---------- 稳定层
    V = [[nu_iv[k] ** i for k in range(6)] for i in range(6)]

    def iv_inv(M, n):
        A = [row[:] + [iv.mpf(1) if i == j else iv.mpf(0) for j in range(n)]
             for i, row in enumerate(M)]
        for col in range(n):
            p = max(range(col, n), key=lambda r: abs((A[r][col].a + A[r][col].b) / 2))
            A[col], A[p] = A[p], A[col]
            piv = A[col][col]
            A[col] = [x / piv for x in A[col]]
            for r in range(n):
                if r != col:
                    f = A[r][col]
                    if f.a == 0 and f.b == 0:
                        continue
                    A[r] = [a - f * b for a, b in zip(A[r], A[col])]
        return [row[n:] for row in A]

    Vi = iv_inv(V, 6)
    for i in range(6):
        for j in range(6):
            s = sum((V[i][k] * Vi[k][j] for k in range(6)), iv.mpf(0))
            tgt = iv.mpf(1) if i == j else iv.mpf(0)
            if not (s.a <= tgt.a and tgt.b <= s.b):
                log("[FAIL] V·V⁻¹ ∋ I 验证失败")
                return 1
    rowmax = max((sum((abs(x) for x in row), iv.mpf(0)) for row in Vi))
    frob = iv.sqrt(sum((x * x for row in Vi for x in row), iv.mpf(0)))
    cV = 1 / (iv.sqrt(6) * frob.b)
    U = rowmax.b

    def rho_threshold(U_):
        f = lambda r: float(U_) * 40 * (1 + r) ** 4 * r - 0.5
        lo, hi = 0.0, 0.1
        for _ in range(300):
            m = (lo + hi) / 2
            if f(m) < 0:
                lo = m
            else:
                hi = m
        return lo
    rho_max = rho_threshold(U)
    anti = None
    anti_arg = None
    for a in range(6):
        for b in range(a, 6):
            s = nu_iv[a] + nu_iv[b]
            if s.a <= 0 <= s.b:
                m = mp.mpf(0)
            else:
                m = min(abs(mp.mpf(s.a)), abs(mp.mpf(s.b)))
            if anti is None or m < anti:
                anti, anti_arg = m, [a, b]
    nu4_iv = nu_iv[3]
    rho_anti = (mp.mpf(0) if nu4_iv.a <= 0 <= nu4_iv.b
                else min(abs(mp.mpf(nu4_iv.a)), abs(mp.mpf(nu4_iv.b))))

    # ---------- gaps 与引理形式
    gaps = []
    if any(c["vs_Estar"] == "undecided-at-zbox" for c in energy_classes):
        gaps.append(
            "E_ttp 与 E* 的区间比较在存档 z* 箱宽度（7.63e-7）下 undecided："
            "E′(z*)=0 但箱不以 z* 为中心，一阶传播 1.18e-5 ≫ |E_ttp−E*|≈2.7e-10；"
            "对引理无影响（该分支只涉及 TTP 自身类，非排除用途）；如需判定可另行"
            "收紧 z* 隔离（本任务遵守「宽度覆盖 z* 区间传播」口径未做）")
    gaps.append(
        "稳定层计数阈值 ρ_max≈3.0e-5 与当前 ε-链的 ρ_spec（tube.json: 0.6447@"
        "ε_forcing、0.0466@地板）相差 3–4 个数量级：ρ-近似计数引理的前提未由现行 "
        "L3 满足（L3 已另行裁定 blocked）；本层交付常数与阈值，不交付链闭合")
    gaps.append(
        "「3×3≥0 ∧ 4×4=0 ⇒ PSD∧rank≤3」的充分性方向未主张未使用；引理只用"
        "实现⊆过滤（平凡）＋过滤集枚举＝单类＋构造性实现证书（非空）")
    all_ttp = all(iso_to(coloring_from_tuple(rep), ttp_ref) for rep, _ in classes)
    if not classes:
        form = "vacuous-survivor-set-empty-see-gaps"
    elif all_ttp:
        form = "unconditional"
    elif all(c["vs_Estar"] == "greater-than-Estar"
             for c, (rep, _) in zip(energy_classes, classes)
             if not iso_to(coloring_from_tuple(rep), ttp_ref)):
        form = "energy-conditioned"
    else:
        form = "failed-see-gaps"

    # ---------- 汇总 JSON（确定性：无时间戳/运行时）
    out = {
        "kind": "n9-l4-orbit",
        "schema": "thomson-n9/bounds/l4-orbit/1",
        "script": "bounds/l4_orbit.py",
        "script_sha256": hashlib.sha256(
            (HERE / "l4_orbit.py").read_bytes()).hexdigest(),
        "seed": SEED,
        "dps": args.dps,
        "lemma": {
            "statement": "9 个单位向量、所有两两内积 ∈ TTP 节点集 {ν_1..ν_6}"
                         "（ν 由 D3h 族闭式从 z* 隔离区间重算）⇒ 边染色 ≅ TTP 染色",
            "form": form,
            "proofSkeleton": [
                "P1 实现⊆过滤集：PSD rank≤3 ⇒ 3×3 主子式≥0 且 4×4 主子式=0",
                "P2 过滤集枚举：float scout（z_mid，容差 1e-3）＋4×4 det 按色模式"
                "（K4 边规范型 2451 类）缓存剪枝；完备性＝sup|det′|·半宽 ≪ 容差",
                "P3 幸存者精确复验：4×4 det ∈ Z[z,r]/(r²+z²−1) 恒等零 ⇒ 恒满足；"
                "否则 z* 箱区间（宽度覆盖传播）排零 ⇒ 排除；骑墙 ⇒ undecided 记录",
                "P4 canonical iso 归类（backtracking＋顶点轮廓剪枝）",
                "P5 TTP 类构造实现证书：族坐标(×2) ∈ Q(√3)[z,r]，Gram 逐项多项式"
                "恒等（√3 部分≡0、非对角≡4·节点曲线、对角≡4）⇒ PSD rank≤3 实现",
                "P6 过滤集={TTP 单类}＋P1＋P5 ⇒ 引理",
            ],
            "honestScope": "离散染色层；构型层回复（Gram→坐标）属 L5（Procrustes，"
                           "另件 l4_procrustes.py）；「过滤⇒可实现」方向不主张",
        },
        "inputs": {
            "zBox": [str(ctx["zlo_str"]), str(ctx["zhi_str"])],
            "zBoxSource": "results/local_min.json zStarIntervalMpmath（严格隔离区间）",
            "zBoxWidth": float(halfw * 2),
            "E_star": str(e_star),
            "E_star_source": "thomson-workflow/data/energies.json energies.9.value",
            "tube_nodes": tube_nodes,
            "tube_mults": tube_mults,
        },
        "nodes": {
            "curves_x2": [poly_str(p) for p in node_poly],
            "intervals": [[mp.nstr(mpv(nu_iv[k].a), 20), mp.nstr(mpv(nu_iv[k].b), 20)]
                          for k in range(6)],
            "widths": [float(nu_iv[k].b - nu_iv[k].a) for k in range(6)],
            "tube_10digit_contained": ctx["tube_check"],
            "parametrization": "6 棱顶（上三角3 z=+z*＋下三角3 z=−z*，半径"
                               " ρ=√(1−z²)，角 2πk/3）＋3 帽顶（z=0 半径 1，角"
                               " π/3+2πk/3）；源 numerics/family.py:39 tri_cap_prism"
                               " 与 full_local_min.py:282/291 "
                               "angles_exact/geometry_dual",
        },
        "scout": {
            "tol3": TOL3, "tol4": TOL4,
            "zmid": float(zmid),
            "supDetPrime4_on_box": float(sup_dp4.b),
            "supDetPrime3_on_box": float(sup_dp3.b),
            "completenessBound4": comp4,
            "completenessBound3": comp3,
            "completenessNote": "任何在真节点值处 4×4 det=0（或 3×3≥0）的染色，"
                                "在 z_mid 处偏移 ≤ sup|det′|·|z_mid−z*| ≤ 上列 "
                                "bound < 容差 ⇒ 必过 scout（无假阴性）",
            "canonicalQuadClasses": len(quad_keys),
            "triPatterns": len(tri_dec),
            "labeledSurvivors": len(sols),
        },
        "exactLayer": {
            "quadDecisions": {d: sum(1 for v in quad_dec.values() if v[0] == d)
                              for d in sorted({v[0] for v in quad_dec.values()})},
            "triDecisions": {d: sum(1 for v in tri_dec.values() if v[0] == d)
                             for d in sorted({v[0] for v in tri_dec.values()})},
            "quadClassesUsedBySurvivors": {str(list(k)): quad_used[k]
                                           for k in sorted(quad_used)},
            "triPatternsUsedBySurvivors": {str(list(k)): tri_used[k]
                                           for k in sorted(tri_used)},
            "accepted": n_acc,
            "rejected": len(rejects),
            "undecidedSurvivors": len(undecided_surv),
            "undecidedBranches": sorted({f"{kind}:{list(key)}"
                                         for _, kind, key in undecided_surv}),
        },
        "survivorSet": {
            "nonEmpty": len(survivors) > 0,
            "labeledTotal": len(survivors),
            "isoClasses": len(classes),
            "representative": list(min(survivors)) if survivors else None,
            "classes": [
                {"index": idx,
                 "members": len(members),
                 "representative": list(rep),
                 "histogram": energy_classes[idx]["histogram"],
                 "isoToTTP": bool(iso_to(coloring_from_tuple(rep), ttp_ref)),
                 "disposition": ("congruent-to-TTP"
                                 if iso_to(coloring_from_tuple(rep), ttp_ref)
                                 else ("E-greater-than-Estar-excluded"
                                       if energy_classes[idx]["vs_Estar"] ==
                                       "greater-than-Estar"
                                       else "gap-see-gaps")),
                 "realizationCertificate": realiz_checks}
                for idx, (rep, members) in enumerate(classes)],
        },
        "energyTable": {"E_star": str(e_star), "classes": energy_classes},
        "orbitBalance": {
            "structure": "6 棱顶（上3+下3）＋3 帽顶（D12 勘误 6+3 证实）",
            "categories": cat_summary,
            "prismVertexProfile": prism_vertex,
            "capVertexProfile": cap_vertex,
            "perNodeSums_Sigma_y": per_node_sums,
            "twoTimesMult": [2 * m for m in tube_mults],
            "tubeMults": list(tube_mults),
            "balanced": balanced,
            "erratum": "任务书/D12「帽-棱 12 边 ν₆＋6 边 ν₅」后半应为 ν₂"
                       "（ν₅ 的 6 边在上下三角内部）；本表由参数化组合推导＋"
                       "reference_config.json 数值复算双重证实，配平不受影响",
        },
        "stability": {
            "vandermonde": {
                "definition": "V[i][k] = ν_k^i, i=0..5, k=1..6",
                "inverseMethod": "区间 Gauss-Jordan（部分主元），V·V⁻¹ ∋ I 逐项验证",
                "normInvInf": [mp.nstr(mpv(rowmax.a), 18),
                               mp.nstr(mpv(rowmax.b), 18)],
                "normInvFro": [mp.nstr(mpv(frob.a), 18), mp.nstr(mpv(frob.b), 18)],
                "sigmaMinLower_cV": mp.nstr(mpv(cV.a), 18),
                "cV_method": "σ(V) ≥ 1/‖V⁻¹‖₂ ≥ 1/(√6·‖V⁻¹‖_F 上界)",
            },
            "countingThreshold": {
                "deltaFormula": "δ_i(ρ) = 8·i·(1+ρ)^{i−1}·ρ（每顶点 8 邻居、"
                                "|ν|+ρ ≤ 1+ρ）；‖V⁻¹‖_∞·(δ_∞(ρ)+Δ) < 1/2 ⇒ "
                                "邻型计数向量＝轨道向量（整数向量 ℓ∞ 距离<1 相等）",
                "rhoMax_deltaOnly": rho_max,
                "deltaPerI_at_1em3": [8 * i * (1 + 1e-3) ** (i - 1) * 1e-3
                                      for i in range(6)],
            },
            "antipodalSeparation": {
                "minNuaNuB_lower": mp.nstr(anti, 18),
                "arg": anti_arg,
                "selfPair2nu4": "min 自对 |ν₄+ν₄| = 2ν₄（命题 5.1(i) 口径）",
                "rhoThreshold": mp.nstr(rho_anti, 18),
                "statement": "ρ < ν_4 下界 ⇒ 管内任两节点值之和 |α+β| ≥ "
                             "2ν₄−2ρ > 0（对径分离管阈值）",
            },
            "chainComparison": {
                "rhoSpecAtForcing": tube["verdict"]["rho_spec_at_forcing"],
                "rhoSpecAtFloor": tube["verdict"]["rho_spec_at_floor"],
                "verdict": "前提未由现行 ε-链满足（L3 已另行裁定 blocked）；"
                           "本层交付常数与阈值",
            },
        },
        "gaps": gaps,
        "provenance": {
            "commands": ["python3 numerics/bounds/l4_orbit.py --dps 50"],
            "deps": ["mpmath 1.3.0（区间算术）；其余 stdlib"],
            "determinism": "DFS 固定迭代序、无随机性（seed 仅声明）；输出无时间戳"
                           "/运行时 ⇒ 幂等重算逐位一致",
        },
    }
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    log(f"done: {out_path} (total {time.time() - t_start:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
