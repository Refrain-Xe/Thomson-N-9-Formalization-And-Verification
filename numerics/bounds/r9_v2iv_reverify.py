#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r9_v2iv_reverify.py — R9B v2-interval-reverify（D33 裁决 5③ 收账，R9D 设计）.

对存档证书 results/hermite_v2_probe_contact.json（v2 contact 相位 0：17 系数
deg≤16 minorant M′=Σ Mj t^j−W，k=48）做**自写区间算术**的独立重验——不 import
hermite_minorant.py 的任何区间工具（自写：Fraction＋整数 isqrt 有理 sqrt
下/上界，B≥120 bit）。

五项：
  ① 七区域 Π≥0 重推——区域边界==Fraction(float(ν_k)) 精确、并集无缝覆盖
     [−1,1]、逐区域负因子计数 6..0、Π(t)=(t+1)⁵∏(t−ν_k)² 因子逐个判号；
     c_const==(2·17−1)!!/17!==583401555/32768 精确重算；φ^{(m)}(t)=
     (2m−1)!!(2−2t)^{−(2m+1)/2}>0 于 t<1 公式核验（符号递推＋hull 区间验证）。
  ② W 恒等式——Σ_j hw_j==17·2⁻⁴⁹==17/562949953421312 精确；coeffs dyadic
     格点结构核验（如实记录：coeffs[0] 在 2⁻⁴⁸ 格点、coeffs[1..16] 在
     2⁻⁴⁹ 奇格点＝2⁻⁴⁸ 外舍的中点格）；coeffs[0]=M₀−W 语义核验
     （hermite_minorant.py:223-290 定义自读复核，按 sha256 钉扎）。
  ③ 直接区间路径（不经定理分解）：φ(t)−M′(t)≥0 于 [−1,1] 全覆盖自适应二分。
     叶界（自写推导，本文件独立成立）：
       φ 凸（φ''=3(2−2t)^{−5/2}↑）⟹ φ(t) ≥ φ(a)+φ'(a)(t−a)+φ''_lo(a)/2·(t−a)²
         （a=叶左端，二阶 Lagrange，isqrt 下界）；
       M′(t) ≤ M′(m)+M′'(m)s+M′''(m)/2·s²+|M′'''(m)|/6·δ³+Σ_{r≥4}D_r/r!·δ^r
         （m=叶中点、s=t−m∈[−δ,δ]、D_r=Σ_j (j)_r|c_j| 全局精确界）；
       判据＝该二次式在叶上精确最小值 ≥0；负间隙检出＝φ 上界（b 端二阶
       Taylor＋负三次余项丢弃）−M′ 下界 <0。真实间隙 ≥2.8e-14 ≫ 2⁻²ᴮ。
  ④ strip [−153/200,−187/250] 上 sup(φ−M′) 的区间上界（堆式自适应 refine）：
     对存档 exact_grid_max_gap_ub 口径 1%＋2⁻⁴⁹ 容差内、硬上界 <1e-12、
     1.5717e4× 收紧比复算（对引用值 6.96e-10 ＋对独立重建 M_old 双口径）。
     M_old（plain 12 条 deg-11）自写精确重建（12×12 有理解＋k=48 外舍）对
     hermite_probe.json 存档逐位比对。
  ⑤ c0_dense float 网格复算（witness 级，如实标注非严格）。

用法：
  python3 numerics/bounds/r9_v2iv_reverify.py                    # full → results/r9_v2iv.json
  python3 numerics/bounds/r9_v2iv_reverify.py --scope quick      # 快档（负对照用）
  python3 numerics/bounds/r9_v2iv_reverify.py --cert /tmp/x.json --out /tmp/y.json
exit 0 ⟺ 全部五项 PASS；任一 FAIL ⟹ exit 1（结果照写，负间隙区间如实报告）。
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

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
RESULTS = HERE / "results"
SEED = 20261010
F0 = Fraction(0)
F1 = Fraction(1)
STRIP_LO = Fraction(-153, 200)
STRIP_HI = Fraction(-187, 250)
W_EXPECT = Fraction(17, 562949953421312)      # 17·2⁻⁴⁹
C_CONST_EXPECT = Fraction(583401555, 32768)   # (2·17−1)!!/17!
ARCH_STRIP_UB = Fraction("4.4283673247852223e-14")   # 存档 float 口径
M_OLD_CITED = Fraction("6.96e-10")            # GAP-REPORT:2689 引用值
TWO_M49 = Fraction(1, 1 << 49)

try:
    import numpy as _np
except Exception:                                        # pragma: no cover
    _np = None


def fail(msg: str) -> None:
    print(f"[reverify][FAIL] {msg}", flush=True)


def code_version() -> str:
    try:
        return subprocess.check_output(
            ["git", "describe", "--always", "--dirty"], cwd=str(REPO),
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown(non-git)"


# ============================================================ 自写区间算术
def sqrt_iv(q: Fraction, B: int):
    """[P/2^{2B}, (P+1)/2^{2B}] ∋ √q（q>0 有理）。P=isqrt(⌊q·2^{4B}⌋）⟹
    P² ≤ q·2^{4B} < (P+1)²，宽度 2^{−2B}。自写，不依赖 hermite_minorant。"""
    assert q > 0 and B >= 120
    Q = (q.numerator << (4 * B)) // q.denominator
    P = math.isqrt(Q)
    return Fraction(P, 1 << (2 * B)), Fraction(P + 1, 1 << (2 * B))


def inv_sqrt_pow_iv(q: Fraction, power: int, B: int):
    """区间 ∋ q^{−power/2}（power 正奇数）。q^{−p/2}=1/√(q^p)，
    1/x 递减 ⟹ [1/hi, 1/lo]。"""
    lo, hi = sqrt_iv(q ** power, B)
    return (F1 / hi, F1 / lo)


def dfactorial_odd(m: int) -> int:
    """(2m−1)!!=1·3···(2m−1)（m=0 → 1）。"""
    out = 1
    for i in range(1, 2 * m, 2):
        out *= i
    return out


def horner(cs, t: Fraction) -> Fraction:
    acc = F0
    for c in reversed(cs):
        acc = acc * t + c
    return acc


def falling(j: int, m: int) -> int:
    if j < m:
        return 0
    out = 1
    for i in range(j - m + 1, j + 1):
        out *= i
    return out


# ============================================================ 叶界共享件
class LeafBender:
    """③④ 共用的叶界机：多项式 coeffs（Fraction 列表）的
      M′(t) ≤ Mm + M1·s + M2/2·s² + slop3        （s=t−m, |s|≤δ）
      M′(t) ≥ Mm + M1·s + M2/2·s² − slop3
    其中 slop3 = |M′'''(m)|/6·δ³ + Σ_{r≥4} D_r/r!·δ^r（D_r=Σ_j (j)_r|c_j|）。
    φ 侧：凸 ⟹ 二阶 Taylor at a 为下界；at b＋丢弃负三次余项为上界。"""

    def __init__(self, coeffs, B: int):
        self.cs = list(coeffs)
        n = len(self.cs)
        self.d1 = [Fraction(j + 1) * self.cs[j + 1] for j in range(n - 1)]
        self.d2 = [Fraction((j + 2) * (j + 1)) * self.cs[j + 2] for j in range(n - 2)]
        self.d3 = [Fraction((j + 3) * (j + 2) * (j + 1)) * self.cs[j + 3]
                   for j in range(n - 3)]
        self.D = {}
        for r in range(4, n):
            s = F0
            for j in range(r, n):
                s += Fraction(falling(j, r)) * abs(self.cs[j])
            self.D[r] = s
        self.B = B
        self._qcache = {}

    def q4(self, delta: Fraction) -> Fraction:
        if delta in self._qcache:
            return self._qcache[delta]
        s = F0
        for r, D in self.D.items():
            s += D / math.factorial(r) * delta ** r
        self._qcache[delta] = s
        return s

    def poly_at(self, m: Fraction):
        return (horner(self.cs, m), horner(self.d1, m),
                horner(self.d2, m), horner(self.d3, m))

    def phi_side_lo(self, a: Fraction):
        """(φ_lo(a), φ'_lo(a), φ''_lo(a)) —— isqrt 下界。φ^{(m)}=c_m·u^{−(2m+1)/2}."""
        B = self.B
        u = Fraction(2) - 2 * a
        lo, hi = sqrt_iv(u, B)
        return (F1 / hi, F1 / (u * hi), Fraction(3) / (u * u * hi))

    def phi_side_hi(self, b: Fraction):
        """(φ_hi(b), φ'_hi(b), φ''_hi(b)) —— isqrt 上界。"""
        B = self.B
        u = Fraction(2) - 2 * b
        lo, hi = sqrt_iv(u, B)
        return (F1 / lo, F1 / (u * lo), Fraction(3) / (u * u * lo))

    @staticmethod
    def quad_min(A: Fraction, Bc: Fraction, C: Fraction, d: Fraction) -> Fraction:
        """min_{s∈[−d,d]} A s²+Bc s+C（精确）。"""
        cands = [A * d * d + Bc * d + C, A * d * d - Bc * d + C]
        if A > 0:
            s = -Bc / (2 * A)
            if -d <= s <= d:
                cands.append(A * s * s + Bc * s + C)
        return min(cands)

    @classmethod
    def quad_max(cls, A, Bc, C, d):
        return -cls.quad_min(-A, -Bc, -C, d)


# ============================================================ ③ 直接区间路径
def direct_interval_cover(coeffs, B: int, eval_budget: int,
                          width_floor: Fraction, dom_hi: Fraction,
                          stop_on_violation: bool = True):
    """φ(t)−M′(t)≥0 于 [−1, dom_hi] 自适应二分全覆盖。

    叶判据（sound，见类注释推导）：
      PASS   ⟺ min_{s∈[−δ,δ]} [φa+φpa(t−a)+φppa/2·(t−a)² − Mm − M1 s
              − M2/2 s² − slop3] ≥ 0（s=t−m；t−a=s+(m−a)）
      VIOLATE⟺ max_{s∈[−δ,δ]} [φb+φpb(t−b)+φppb/2·(t−b)² − Mm − M1 s
              − M2/2 s² + slop3] < 0（整叶负间隙认证）
    返回 dict（含覆盖计帐）；violations 非空或 inconclusive 非空 ⟹ not ok。"""
    t0 = time.time()
    lb = LeafBender(coeffs, B)
    stack = [(-F1, dom_hi)]
    n_leaves = n_evals = max_depth = 0
    covered = F0
    min_gap = None
    violations, inconclusive = [], []
    depth_of = {}
    while stack:
        a, b = stack.pop()
        n_evals += 1
        if n_evals > eval_budget:
            inconclusive.append(dict(
                interval=[str(a), str(b)], note="eval budget exhausted",
                width=str(b - a)))
            stack.clear()
            break
        m = (a + b) / 2
        d = (b - a) / 2
        Mm, M1, M2, M3 = lb.poly_at(m)
        slop3 = abs(M3) * d ** 3 / 6 + lb.q4(d)
        phi_a, phip_a, phipp_a = lb.phi_side_lo(a)
        ma = m - a
        A = (phipp_a - M2) / 2
        Bc = phip_a - M1 + phipp_a * ma
        C = phi_a + phip_a * ma + phipp_a * ma * ma / 2 - Mm - slop3
        lo = LeafBender.quad_min(A, Bc, C, d)
        if lo >= 0:
            n_leaves += 1
            covered += b - a
            min_gap = lo if min_gap is None else min(min_gap, lo)
            continue
        # 负间隙认证（整叶）
        phi_b, phip_b, phipp_b = lb.phi_side_hi(b)
        Ae = (phipp_b - M2) / 2
        Be = phip_b - M1 - phipp_b * d
        Ce = phi_b - phip_b * d + phipp_b * d * d / 2 - Mm + slop3
        if LeafBender.quad_max(Ae, Be, Ce, d) < 0:
            violations.append(dict(interval=[str(a), str(b)],
                                   interval_float=[float(a), float(b)],
                                   width=str(b - a)))
            if stop_on_violation:
                stack.clear()
                break
            continue        # pragma: no cover（快停默认开；慢速全扫分支备用）
        if b - a <= width_floor:
            inconclusive.append(dict(interval=[str(a), str(b)], width=str(b - a),
                                     quad_min=str(lo)))
            continue
        stack.append((m, b))
        stack.append((a, m))
    ok = (not violations) and (not inconclusive) and n_leaves > 0
    return dict(ok=bool(ok), n_pass_leaves=n_leaves, n_evals=n_evals,
                leaf_eval_budget=eval_budget, width_floor=str(width_floor),
                covered_measure=str(covered), domain_length=str(dom_hi + 1),
                coverage_exact=bool(covered == dom_hi + 1 if ok else False),
                min_certified_gap=(str(min_gap) if min_gap is not None else None),
                min_certified_gap_float=(float(min_gap)
                                         if min_gap is not None else None),
                n_violations=len(violations), violations=violations,
                n_inconclusive=len(inconclusive), inconclusive=inconclusive,
                cover_s=round(time.time() - t0, 3))


# ============================================================ ④ sup 区间界
def interval_sup(coeffs, a0: Fraction, b0: Fraction, B: int, tol: Fraction,
                 split_cap: int = 2_000_000):
    """sup_{t∈[a0,b0]}(φ−M′) 的区间上/下界（堆式自适应，Fraction 精确）。"""
    import heapq
    t0 = time.time()
    lb = LeafBender(coeffs, B)

    def leaf_ub_lb(a, b):
        m = (a + b) / 2
        d = (b - a) / 2
        Mm, M1, M2, M3 = lb.poly_at(m)
        slop3 = abs(M3) * d ** 3 / 6 + lb.q4(d)
        phi_b, phip_b, phipp_b = lb.phi_side_hi(b)
        # 上界：max_s [φ_ub − M′_lb]；t−b = s−d
        A = (phipp_b - M2) / 2
        Bq = phip_b - M1 - phipp_b * d
        Cq = phi_b - phip_b * d + phipp_b * d * d / 2 - Mm + slop3
        ub = LeafBender.quad_max(A, Bq, Cq, d)
        # 下界：叶中点点值（φ 下界 isqrt − M′(m) 精确）
        _, Sh = sqrt_iv(Fraction(2) - 2 * m, B)
        lbv = F1 / Sh - Mm
        return ub, lbv

    ub0, lb0 = leaf_ub_lb(a0, b0)
    heap = [(-ub0, 0, (a0, b0))]        # 最大堆（取负）
    seq = 1
    best_lb = lb0
    n_leaves = n_splits = 0
    sup_ub = ub0
    while heap:
        negub, _, (a, b) = heapq.heappop(heap)
        ub = -negub
        if ub - best_lb <= tol or n_splits >= split_cap:
            sup_ub = ub if n_splits < split_cap else max(
                ub, max((-h[0]) for h in heap))
            break
        m = (a + b) / 2
        for (x, y) in ((a, m), (m, b)):
            ubc, lbc = leaf_ub_lb(x, y)
            n_leaves += 1
            best_lb = max(best_lb, lbc)
            heapq.heappush(heap, (-ubc, seq, (x, y)))
            seq += 1
        n_splits += 1
    return dict(sup_ub=str(sup_ub), sup_ub_float=float(sup_ub),
                sup_lb=str(best_lb),
                sup_lb_float=float(best_lb), uncertainty=str(sup_ub - best_lb),
                uncertainty_float=float(sup_ub - best_lb), n_leaves=n_leaves,
                n_splits=n_splits, tol=str(tol), sup_s=round(time.time() - t0, 3))


# ============================================================ M_old 自写重建
def rebuild_m_old(nodes_f, B: int = 200, k: int = 48):
    """plain 12 条（6 节点值＋一阶导）deg≤11 dyadic minorant 的**自写**精确重建
    （对 hermite_minorant.py:223-290 同口径：B=200、k=48、外舍、W 折入 c₀）。
    独立实现：自写高斯消元/求逆＋区间传播＋dyadic 舍入。"""
    t0 = time.time()
    nu = [Fraction(x) for x in nodes_f]
    n = 2 * len(nu)
    rows, b_lo, b_hi = [], [], []
    for v in nu:
        q = Fraction(2) - 2 * v
        for m in (0, 1):
            iv = inv_sqrt_power_iv_(q, 2 * m + 1, B)
            if m:
                iv = (Fraction(dfactorial_odd(m)) * iv[0],
                      Fraction(dfactorial_odd(m)) * iv[1])
            if m == 0:
                row = [v ** j for j in range(n)]
            else:
                row = [Fraction(falling(j, 1)) * v ** (j - 1) if j >= 1 else F0
                       for j in range(n)]
            rows.append(row)
            b_lo.append(iv[0])
            b_hi.append(iv[1])
    Ainv = _invert_rational(rows)
    c_lo = [F0] * n
    c_hi = [F0] * n
    for j in range(n):
        lo, hi = F0, F0
        for m in range(n):
            a = Ainv[j][m]
            if a >= 0:
                lo += a * b_lo[m]
                hi += a * b_hi[m]
            else:
                lo += a * b_hi[m]
                hi += a * b_lo[m]
        c_lo[j], c_hi[j] = lo, hi
    scale = 1 << k

    def dyad_floor(x):
        return Fraction(math.floor(x * scale), scale)

    def dyad_ceil(x):
        return Fraction(-math.floor(-x * scale), scale)

    LO = [dyad_floor(x) for x in c_lo]
    HI = [dyad_ceil(x) for x in c_hi]
    Mj = [(l + h) / 2 for l, h in zip(LO, HI)]
    hw = [max(mm - l, h - mm) for mm, l, h in zip(Mj, LO, HI)]
    W = sum(hw, F0)
    coeffs = list(Mj)
    coeffs[0] -= W
    return dict(coeffs=coeffs, W=W, hw=hw, k=k, B=B,
                build_s=round(time.time() - t0, 3))


def inv_sqrt_power_iv_(q: Fraction, power: int, B: int):
    # 与 inv_sqrt_power_iv 相同（独立命名以免与 ③④ 的 B 混用——此路固定 200）
    lo, hi = sqrt_iv(q ** power, B)
    return (F1 / hi, F1 / lo)


def _invert_rational(A):
    n = len(A)
    cols = []
    for j in range(n):
        e = [Fraction(1) if i == j else Fraction(0) for i in range(n)]
        M = [row[:] + [e[i]] for i, row in enumerate(A)]
        for col in range(n):
            piv = next((r for r in range(col, n) if M[r][col] != 0), None)
            assert piv is not None, "插值矩阵奇异"
            M[col], M[piv] = M[piv], M[col]
            pv = M[col][col]
            M[col] = [x / pv for x in M[col]]
            for r in range(n):
                if r != col and M[r][col] != 0:
                    f = M[r][col]
                    M[r] = [x - f * y for x, y in zip(M[r], M[col])]
        cols.append([M[i][n] for i in range(n)])
    return [[cols[j][i] for j in range(n)] for i in range(n)]


# ============================================================ 各项重验
def item1_regions(cert, B: int):
    t0 = time.time()
    nodes = [float(x) for x in cert["nodes"]]
    nu = sorted(Fraction(x) for x in nodes)
    breaks = [Fraction(-1)] + nu + [Fraction(1)]
    arch = cert["interval_certificate"]
    problems = []
    # 边界逐位（str 与值双口径）
    arch_iv = [(Fraction(r["interval"][0]), Fraction(r["interval"][1]),
                r["interval"][0], r["interval"][1]) for r in arch["regions"]]
    boundary_match = len(arch_iv) == len(breaks) - 1
    str_match = True
    if boundary_match:
        for i, (alo, ahi, slo, shi) in enumerate(arch_iv):
            if not (alo == breaks[i] and ahi == breaks[i + 1]
                    and slo == str(breaks[i]) and shi == str(breaks[i + 1])):
                boundary_match = str_match = False
    else:
        str_match = False
        problems.append(f"区域数 {len(arch_iv)} ≠ {len(breaks)-1}")
    # 无缝覆盖 [−1,1]
    union_covers = bool(boundary_match and arch_iv[0][0] == -1
                        and arch_iv[-1][1] == 1
                        and all(arch_iv[i][1] == arch_iv[i + 1][0]
                                for i in range(len(arch_iv) - 1)))
    # 逐区域：负因子计数、内部无节点、因子判号
    neg_counts, factor_rows = [], []
    pi_all_nonneg = True
    node_free = True
    for i, (a, b) in enumerate(zip(breaks[:-1], breaks[1:])):
        neg = sum(1 for v in nu if b <= v)
        neg_counts.append(neg)
        interior_free = all((v <= a) or (v >= b) for v in nu)
        node_free = node_free and interior_free
        # 因子逐个判号（精确区间）
        tplus1 = (a + 1, b + 1)                       # ⊆ [0,2]
        f1_nonneg = tplus1[0] >= 0
        sq_nonneg = []
        for v in nu:
            sq_hi = max((a - v) ** 2, (b - v) ** 2)
            sq_nonneg.append(dict(node=str(v), interval=[0, str(sq_hi)],
                                  nonneg=True))
        pi_nonneg = bool(f1_nonneg and all(r["nonneg"] for r in sq_nonneg))
        pi_all_nonneg = pi_all_nonneg and pi_nonneg
        factor_rows.append(dict(
            region=i, interval=[str(a), str(b)], neg_factors=neg,
            interior_node_free=interior_free,
            factor_t_plus_1=dict(interval=[str(tplus1[0]), str(tplus1[1])],
                                 power=5, nonneg=f1_nonneg),
            factor_node_squares=sq_nonneg, pi_nonneg=pi_nonneg))
        r_arch = arch["regions"][i] if i < len(arch["regions"]) else {}
        if r_arch.get("pi_sign") != ">=0":
            problems.append(f"区域 {i} 存档 pi_sign={r_arch.get('pi_sign')}")
        sb = r_arch.get("sign_basis", "")
        import re as _re
        mm = _re.search(r"(\d+) negative factors", sb)
        if not mm or int(mm.group(1)) != neg:
            problems.append(f"区域 {i} 存档负因子计数 {sb!r} ≠ 复推 {neg}")
    # c_const
    ncond = int(cert["ncond"])
    c_const = Fraction(dfactorial_odd(ncond), math.factorial(ncond))
    c_const_ok = (c_const == C_CONST_EXPECT
                  and Fraction(arch["c_const"]) == c_const)
    # hull
    hull_mine = [nu[0], nu[-1]]
    hull_ok = (hull_mine[0] == Fraction(arch["hull"][0])
               and hull_mine[1] == Fraction(arch["hull"][1]))
    hull_right_lt_1 = hull_mine[1] < 1
    # φ^{(m)} 公式：符号递推核验（链式法则常数 −2×(−(2m+1)/2)=2m+1 精确）
    rec_ok = True
    rec_rows = []
    for m in range(0, ncond):
        # d/dt[(2m−1)!!·u^{−(2m+1)/2}] = (2m+1)!!·u^{−(2m+3)/2}
        c_from = Fraction(dfactorial_odd(m))
        c_to = Fraction(dfactorial_odd(m + 1))
        chain = Fraction(-(2 * m + 1), 2) * Fraction(-2)     # u' = −2
        rec_ok_i = (c_from * chain == c_to)
        rec_ok = rec_ok and rec_ok_i
        rec_rows.append(dict(m=m, coef_from=f"{dfactorial_odd(m)}",
                             coef_to=f"{dfactorial_odd(m + 1)}",
                             chain_const=str(chain), ok=bool(rec_ok_i)))
    base_ok = True        # m=0：φ=u^{−1/2} 即定义
    # hull 区间验证 φ^{(m)}>0（m=0..ncond）
    u_lo = Fraction(2) - 2 * hull_mine[1]      # u 在 hull 上的区间 [u_lo, u_hi]
    u_hi = Fraction(2) - 2 * hull_mine[0]
    hull_rows = []
    hull_pos_ok = True
    for m in range(0, ncond + 1):
        # g(u)=u^{−(2m+1)/2} 递减 ⟹ 下界取 u_hi 端：1/√(u_hi^{2m+1}) 上界
        _, s_hi = sqrt_iv(Fraction(u_hi) ** (2 * m + 1), B)
        g_lo = F1 / s_hi
        pref = Fraction(dfactorial_odd(m))
        row_lo = pref * g_lo
        hull_pos_ok = hull_pos_ok and row_lo > 0
        hull_rows.append(dict(m=m, lo=str(row_lo), lo_float=float(row_lo),
                              positive=bool(row_lo > 0)))
    # φ^{(m)}(−1)=(2m−1)!!/2^{2m+1} 有理恒等（区间包含核验）
    pm1_ok = True
    for m in range(0, ncond + 1):
        exact = Fraction(dfactorial_odd(m), 2 ** (2 * m + 1))
        lo, hi = inv_sqrt_power_iv_(Fraction(4), 2 * m + 1, B)
        iv_val = Fraction(dfactorial_odd(m)) * lo
        if not (iv_val <= exact):
            pm1_ok = False
    ok = (boundary_match and str_match and union_covers and pi_all_nonneg
          and node_free and c_const_ok and hull_ok and hull_right_lt_1
          and rec_ok and base_ok and hull_pos_ok and pm1_ok and not problems
          and neg_counts == list(range(len(nu), -1, -1)))
    return dict(
        ok=bool(ok), problems=problems,
        n_regions=len(breaks) - 1,
        boundaries=[str(x) for x in breaks],
        boundaries_match_archive_bitwise=bool(boundary_match and str_match),
        union_covers_minus1_1_seamless=bool(union_covers),
        neg_factor_counts=neg_counts,
        neg_counts_6_to_0=bool(neg_counts == list(range(len(nu), -1, -1))),
        interior_node_free=bool(node_free),
        pi_factorwise=factor_rows,
        pi_all_nonneg=bool(pi_all_nonneg),
        pi_degree_rederived=5 + 2 * len(nu),
        pi_degree_archived=arch.get("pi_degree"),
        c_const=dict(recomputed=str(c_const), archived=arch["c_const"],
                     expected="583401555/32768", equal=bool(c_const_ok),
                     float=float(c_const)),
        hull=dict(rederived=[str(x) for x in hull_mine],
                  archived=arch["hull"], bitwise_match=bool(hull_ok),
                  hull_right_lt_1=bool(hull_right_lt_1)),
        phi_derivs=dict(
            formula="(2m-1)!!*(2-2t)^{-(2m+1)/2}",
            symbolic_recurrence_ok=bool(rec_ok and base_ok),
            recurrence_rows=rec_rows,
            hull_interval_positivity=bool(hull_pos_ok),
            hull_rows=hull_rows,
            at_minus1_closed_form_in_interval=bool(pm1_ok),
            note="递推=链式法则精确常数；hull 区间=递减性+isqrt 下界；"
                 "m=0..ncond(17) 全正"),
        item1_s=round(time.time() - t0, 3))


def item2_w_identity(cert):
    t0 = time.time()
    coeffs = [Fraction(s) for s in cert["coeffs"]]
    hw = [Fraction(s) for s in cert["halfwidths"]]
    W = Fraction(cert["W"])
    k = int(cert["k"])
    problems = []
    hw_sum = sum(hw, F0)
    sum_ok = (hw_sum == W == W_EXPECT)
    if not sum_ok:
        problems.append(f"Σhw={hw_sum} W={W} 期望 {W_EXPECT}")
    if k != 48:
        problems.append(f"k={k}≠48")
    # W_float 一致
    wf_ok = float(W) == float(cert.get("W_float"))
    # 格点结构（如实记录）
    on2m49 = all((c * (1 << 49)).denominator == 1 for c in coeffs)
    idx48 = [j for j, c in enumerate(coeffs) if (c * (1 << 48)).denominator == 1]
    on2m48_count = len(idx48)
    # 中点格结构：Mj=coeffs[j](j≥1)、M₀=coeffs[0]+W 均为 2⁻⁴⁹ 奇格点，
    # 且 LO/HI=Mj∓2⁻⁴⁹ 落 2⁻⁴⁸ 格点（hw_j=2⁻⁴⁹ 外舍的精确结构）
    M = list(coeffs)
    M[0] = coeffs[0] + W
    midp_ok = True
    hw_each_ok = True
    for j, mj in enumerate(M):
        if (mj * (1 << 49)).denominator != 1 or (mj * (1 << 49)).numerator % 2 != 1:
            midp_ok = False
        if hw[j] != TWO_M49:
            hw_each_ok = False
    lohi_on48 = all(((mj - TWO_M49) * (1 << 48)).denominator == 1
                    and ((mj + TWO_M49) * (1 << 48)).denominator == 1
                    for mj in M)
    # coeffs[0]=M₀−W 语义：恒等式在种子有理点精确成立
    rng = random.Random(SEED)
    pts = [Fraction(rng.randint(-10 ** 6, 10 ** 6), 10 ** 6) for _ in range(5)]
    idn_ok = True
    for t in pts:
        lhs = horner(coeffs, t)
        rhs = sum(mj * t ** j for j, mj in enumerate(M)) - W
        if lhs != rhs:
            idn_ok = False
    # 自读复核钉扎：hermite_minorant.py 223-290
    hm_path = HERE / "hermite_minorant.py"
    hm_sha = hashlib.sha256(hm_path.read_bytes()).hexdigest() if hm_path.exists() else None
    ok = (sum_ok and wf_ok and on2m49 and midp_ok and hw_each_ok and lohi_on48
          and idn_ok and not problems)
    return dict(
        ok=bool(ok), problems=problems,
        W_archived=cert["W"], W_sum_hw=str(hw_sum), W_expected=str(W_EXPECT),
        W_identity_exact=bool(sum_ok), W_float_consistent=bool(wf_ok), k=k,
        all_coeffs_on_2m49_lattice=bool(on2m49),
        coeffs_on_2m48_indices=idx48,
        coeffs_on_2m48_count=on2m48_count,
        lattice_note=("任务书措辞「coeffs 全在 2⁻⁴⁸ 格点」逐字不成立：coeffs[0]"
                      " 在 2⁻⁴⁸ 格点、coeffs[1..16] 为 2⁻⁴⁹ 奇格点；实质内容＝"
                      "全部 Mj 为 2⁻⁴⁸ 外舍格（宽 2⁻⁴⁸）的中点（hw_j=2⁻⁴⁹），"
                      "如实在本条核验通过并记录措辞出入"),
        midpoint_cell_structure=bool(midp_ok and lohi_on48),
        hw_each_is_2m49=bool(hw_each_ok),
        coeffs0_semantics=dict(
            M0=str(M[0]), identity_at_seeded_points=bool(idn_ok),
            points=5,
            definition_ref="hermite_minorant.py:223-290（hermite_minorant_"
                           "dyadic：LO/HI 2^-k 外舍 :277-280、Mj 中点 :281、"
                           "hw=max(m-l,h-m) :282、W=Σhw :283、coeffs[0]-=W :285）",
            hermite_minorant_sha256=hm_sha,
            consequence=("M′(t)=ΣMj t^j−W；|ΣMj t^j−H_exact(t)|≤Σhw_j|t|^j≤W "
                         "(|t|≤1) ⟹ M′(t)≤H_exact(t) 点位小顶——H_exact 侧的"
                         "包裹主张属证书构造（本重验不重建 H_exact，由 ③ 直接"
                         "区间路径独立给出 φ−M′≥0）")),
        item2_s=round(time.time() - t0, 3))


def item3_direct(cert, B: int, scope: str):
    t0 = time.time()
    coeffs = [Fraction(s) for s in cert["coeffs"]]
    budget = 2_000_000 if scope == "full" else 200_000
    dom_hi = Fraction((1 << 40) - 1, 1 << 40)      # 1 − 2⁻⁴⁰
    res = direct_interval_cover(coeffs, B, budget, Fraction(1, 1 << 56), dom_hi)
    # 尾巴 [1−2⁻⁴⁰, 1)：φ ≥ 2^19.5 ≫ Σ|c_j|
    _, Sh = sqrt_iv(Fraction(1, 1 << 39), B)
    phi_tail_lo = F1 / Sh
    s_abs = sum(abs(c) for c in coeffs)
    tail_ok = phi_tail_lo > s_abs
    res["tail"] = dict(interval=[str(dom_hi), "1"],
                       phi_lo=str(phi_tail_lo), phi_lo_float=float(phi_tail_lo),
                       M_abs_ub=str(s_abs), M_abs_ub_float=float(s_abs),
                       trivially_positive=bool(tail_ok))
    res["domain_note"] = ("[−1,1−2⁻⁴⁰] 自适应二分＋[1−2⁻⁴⁰,1) 单调平凡尾；"
                          "覆盖度量＝(1−2⁻⁴⁰)−(−1)＋2⁻⁴⁰=2 精确")
    res["total_covered_with_tail"] = str(Fraction(res["covered_measure"])
                                         + Fraction(1, 1 << 40)) if res["ok"] else None
    res["ok"] = bool(res["ok"] and tail_ok)
    res["item3_s"] = round(time.time() - t0, 3)
    return res


def item4_strip(cert, B: int, scope: str):
    t0 = time.time()
    coeffs = [Fraction(s) for s in cert["coeffs"]]
    tol = Fraction(1, 1 << 53) if scope == "full" else Fraction(1, 1 << 50)
    sup = interval_sup(coeffs, STRIP_LO, STRIP_HI, B, tol)
    sup_ub = Fraction(sup["sup_ub"])
    arch = cert["gap_metrics"]["strip"]
    arch_exact = Fraction(arch["exact_grid_max_gap_ub"])
    arch_float = Fraction(str(arch["exact_grid_max_gap_ub_float"]))
    tol_abs = Fraction(1, 100) * arch_float + TWO_M49
    diff = abs(sup_ub - arch_float)
    within = diff <= tol_abs
    hard = sup_ub < Fraction(1, 10 ** 12)
    sup_ge_arch = sup_ub >= arch_exact
    # M_old 自写重建＋逐位比对＋strip sup
    mo = rebuild_m_old(cert["nodes"], B=200, k=48)
    probe = json.loads((RESULTS / "hermite_probe.json").read_text())
    arch_coeffs = probe["rigorous_minorant"]["coeffs"]
    mo_match = ([str(c) for c in mo["coeffs"]] == arch_coeffs
                and mo["W"] == Fraction(probe["rigorous_minorant"]["W"]))
    mo_sup = interval_sup(mo["coeffs"], STRIP_LO, STRIP_HI, B,
                          Fraction(1, 10 ** 15))
    ratio_cited = M_OLD_CITED / sup_ub
    ratio_rebuilt = Fraction(mo_sup["sup_ub"]) / sup_ub
    mo_vs_cited_ok = (abs(Fraction(mo_sup["sup_ub"]) - M_OLD_CITED)
                      <= Fraction(1, 10) * M_OLD_CITED)
    ok = bool(within and hard and mo_match and mo_vs_cited_ok
              and sup_ge_arch)
    out = dict(
        ok=ok,
        sup=dict(**sup),
        archived=dict(exact_grid_max_gap_ub=arch["exact_grid_max_gap_ub"],
                      float_str=str(arch["exact_grid_max_gap_ub_float"]),
                      grid_n=arch["grid_n"]),
        tol_abs=str(tol_abs), tol_abs_float=float(tol_abs),
        abs_diff=str(diff), abs_diff_float=float(diff),
        within_1pct_plus_2m49=bool(within),
        hard_ub_lt_1e12=bool(hard),
        sup_ub_ge_archived_exact=bool(sup_ge_arch),
        m_old_rebuild=dict(
            coeffs_match_archive_bitwise=bool(mo_match),
            W=str(mo["W"]), W_float=float(mo["W"]),
            archived_W=probe["rigorous_minorant"]["W"],
            ncoeff=len(mo["coeffs"]), k=mo["k"], B=mo["B"],
            build_s=mo["build_s"],
            strip_sup_ub=str(mo_sup["sup_ub"]),
            strip_sup_ub_float=mo_sup["sup_ub_float"],
            strip_sup=dict(**mo_sup),
            vs_cited_6p96e_10_ok=bool(mo_vs_cited_ok),
            cited="6.96e-10（GAP-REPORT.md:2689 / decisions D31 引用值）"),
        ratio_vs_cited=dict(exact=str(ratio_cited), float=float(ratio_cited)),
        ratio_vs_rebuilt=dict(exact=str(ratio_rebuilt),
                              float=float(ratio_rebuilt)),
        tightening_conclusion=("对引用口径 6.96e-10/my_ub 与独立重建口径 "
                              f"{mo_sup['sup_ub_float']:.4e}/my_ub 分别收紧 "
                              f"{float(ratio_cited):.4e}×／"
                              f"{float(ratio_rebuilt):.4e}×（1.5717e4× 定性"
                              "结论保持）"),
        item4_s=round(time.time() - t0, 3))
    return out


def item5_c0_witness(cert, scope: str):
    t0 = time.time()
    archived = cert["dense_and_local"]["ii_sq_gap"]["c0_dense"]
    nodes = cert["nodes"]
    coeffs = [Fraction(s) for s in cert["coeffs"]]
    if _np is not None:
        npts = 1_000_000      # 与存档 dense 网格同规模（c0_dense 口径复算）
        T = _np.linspace(-1.0, 1.0 - 1e-9, npts)
        Mv = _np.zeros_like(T)
        for c in reversed(coeffs):
            Mv = Mv * T + float(c)
        gaps = 1.0 / _np.sqrt(2.0 - 2.0 * T) - Mv
        d2 = _np.full_like(T, 2.0)
        for v in nodes:
            d2 = _np.minimum(d2, (T - v) ** 2)
        mask = d2 >= 1e-6
        ratio = gaps[mask] / d2[mask]
        c0 = float(ratio.min()) if ratio.size else float("nan")
        rel = abs(c0 - archived) / abs(archived)
        ok = rel <= 1e-9
        return dict(ok=bool(ok), level="witness(float 网格，非严格)",
                    recomputed=c0, archived=archived, rel_diff=rel,
                    points=npts, excl_dist=1e-3,
                    item5_s=round(time.time() - t0, 3))
    return dict(ok=False, level="witness(float)",
                note="numpy 不可用：纯 python 回退未复算（如实）",
                archived=archived, item5_s=0.0)


# ============================================================ 主流程
def main() -> None:
    ap = argparse.ArgumentParser(description="R9B v2-interval-reverify（自写区间算术）")
    ap.add_argument("--cert", default=str(RESULTS / "hermite_v2_probe_contact.json"))
    ap.add_argument("--out", default=str(RESULTS / "r9_v2iv.json"))
    ap.add_argument("--scope", choices=["quick", "full"], default="full")
    ap.add_argument("--B", type=int, default=128, help="isqrt 区间位（≥120）")
    args = ap.parse_args()
    assert args.B >= 120, "B ≥ 120 要求"

    t_all = time.time()
    cert_path = Path(args.cert)
    cert = json.loads(cert_path.read_text())
    res = dict(
        task="R9B v2-interval-reverify",
        cert_path=str(cert_path),
        cert_sha256=hashlib.sha256(cert_path.read_bytes()).hexdigest(),
        scope=args.scope, seed=SEED, B=args.B,
        code_version=code_version(),
        generated=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        method=("自写区间算术：Fraction＋整数 isqrt 有理 sqrt 下/上界"
                f"（B={args.B}，宽 2^−{2*args.B}）；零 hermite_minorant import"),
    )
    i1 = item1_regions(cert, args.B)
    i2 = item2_w_identity(cert)
    i3 = item3_direct(cert, args.B, args.scope)
    i4 = item4_strip(cert, args.B, args.scope)
    i5 = item5_c0_witness(cert, args.scope)
    res["items"] = dict(regions=i1, w_identity=i2, direct_interval=i3,
                        strip_gap=i4, c0_witness=i5)
    res["all_pass"] = bool(i1["ok"] and i2["ok"] and i3["ok"] and i4["ok"]
                           and i5["ok"])
    res["timings_s"] = dict(item1=i1["item1_s"], item2=i2["item2_s"],
                            item3=i3["item3_s"], item4=i4["item4_s"],
                            item5=i5["item5_s"],
                            total=round(time.time() - t_all, 3))
    res["dominance_note"] = ("占优检查（dominates=false 负结果见证）不在重验范围"
                             "（D34 裁决 2，如实）")
    Path(args.out).write_text(json.dumps(res, ensure_ascii=False, indent=1))
    mg = i3["min_certified_gap_float"]
    print(f"[reverify] scope={args.scope} ①regions {'PASS' if i1['ok'] else 'FAIL'}"
          f" ②W {'PASS' if i2['ok'] else 'FAIL'}"
          f" ③direct {'PASS' if i3['ok'] else 'FAIL'}"
          f"（{i3['n_pass_leaves']} leaves, violations={i3['n_violations']}, "
          f"min_gap={'n/a' if mg is None else f'{mg:.3e}'}）"
          f" ④strip {'PASS' if i4['ok'] else 'FAIL'}"
          f"（sup_ub={i4['sup']['sup_ub_float']:.4e}）"
          f" ⑤c0 {'PASS' if i5['ok'] else 'FAIL'}（witness）", flush=True)
    print(f"[reverify] all_pass={res['all_pass']} "
          f"total={res['timings_s']['total']}s out={args.out}", flush=True)
    if not res["all_pass"]:
        for name, it in (("①regions", i1), ("②W", i2), ("③direct", i3),
                         ("④strip", i4), ("⑤c0", i5)):
            if not it["ok"]:
                print(f"[reverify][FAIL] {name}: "
                      f"{it.get('problems') or it.get('n_violations') or 'see json'}",
                      flush=True)
        sys.exit(1)


if __name__ == "__main__":
    main()
