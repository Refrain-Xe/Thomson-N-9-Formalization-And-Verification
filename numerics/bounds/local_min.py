#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Thomson N=9 triCapPrism 族内严格局部极小的区间算术验证。

对象：D3h 三帽三棱柱族（family.py 的 tri_cap_prism(z)，z ∈ (0,1)）的能量 E(z)。
E(z) 的精确闭式（按 36 对距离在 z 处的取值分类，ρ = √(1−z²)）：

    12 对  d² = 2 − ρ      顶/底三角与赤道帽、方位差 ±π/3（水平² = ρ²+1−ρ，加 z² 得 2−ρ）
     6 对  d² = 2 + 2ρ     顶/底三角与赤道帽、方位差 π
     6 对  d² = 3ρ²        顶三角内 3 对 + 底三角内 3 对
     3 对  d   = 2z        棱柱竖边
     3 对  d   = √3        赤道帽三角内
     6 对  d² = 3 + z²     顶底三角间斜线
    E(z) = 12/√(2−ρ) + 6/√(2+2ρ) + 6/√(3(1−z²)) + 3/(2z) + √3 + 6/√(3+z²)

本脚本用 mpmath 的区间算术（mpmath.iv，外向舍入）验证：

  1) z* 严格隔离：E′ 在初始括号（默认 [0.6, 0.8]）两端严格变号（区间端点严格
     定号），二分至隔离区间宽度 ≤ TARGET_WIDTH（默认 1e-6 ≤ 要求的 1e-4），
     端点处 |E′| 有显式正下界；
  2) 族内严格局部极小：E″ 在隔离区间上整区间 > 0 ⇒ E′ 在其上严格递增 ⇒
     隔离区间内 E′ 的零点唯一且 E′ 由负变正 ⇒ z* 是族内严格局部极小；
  3) 交叉复核（抓实现错误的独立必要条件，全部区间算术）：
       a. 闭式 vs 构型直接求和：若干测试区间上两个区间 enclosure 必须相交
          （直接求和按定义逐对算 36 个距离，不含任何闭式推导）；
       b. MVT 差商：E 的一阶差商 enclosure 必须严格落在两端点 E′ enclosure
          之间（E″ > 0 ⇒ E′ 严格增，MVT 点在内部）；
       c. 二阶差商：二阶均差 enclosure = E″(η)/2 必须落在 ½·E″(隔离区间)
          enclosure（加 1e-15 数值余量）内；
  4) 族最优能量对照：E(隔离区间) 与 thomson-workflow/data/energies.json 的
     E*(N=9, highPrecision) 距离 ≤ 1e-8。

E′、E″ 不用手推公式：闭式 E(z) 以【二阶前向自动微分】（区间上的三元组
(value, d¹, d²)，乘法/求逆/开方链式法则精确代数）求值，区间求值由包含单调性
给出 E、E′、E″ 在区间上的 enclosure。

--selftest 负对照：(i) 在错误区间 z ∈ [0.5, 0.6]（E′ 两端严格同号）上跑同一套
隔离断言路径，变号断言必须触发；(ii) 以篡改的 E*（真值 + 1e-3）跑能量对照
断言，也必须触发。仅当正向验证全部通过且两个负对照都按预期失败才 exit 0；
任何断言失败即 sys.exit(1)。

输出：bounds/results/local_min.json。
用法：python3 numerics/bounds/local_min.py [--selftest] [--width 1e-6] [--out PATH]
依赖：mpmath >= 1.3（本机已装）。
"""
from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from decimal import Decimal
from pathlib import Path

import mpmath
from mpmath import iv, mp

# ------------------------------------------------------------------ 配置
IV_DPS = 40                       # 区间算术工作精度（十进制位）
BRACKET = ("0.6", "0.8")          # 初始变号括号（E′(0.6)<0<E′(0.8) 待区间断言）
TARGET_WIDTH = "1e-6"             # 隔离区间目标宽度上限（要求 ≤ 1e-4）
WRONG_INTERVAL = ("0.5", "0.6")   # 负对照：E′ 严格同号的错误区间
E_STAR_TOL = 1e-8                 # E(隔离区间) 与 energies.json E* 的距离上限
EXPECTED_Z = 0.70365              # 文档引用常数（family.py 同源），容差 1e-3
Z_TOL = 1e-3
RELAX = 1e-15                     # 均差复核的数值余量（ enclosure 宽度量级 ~1e-17）
ENERGIES_FILE = ("..", "thomson-workflow", "data", "energies.json")  # 相对本文件

REPO_ROOT = Path(__file__).resolve().parents[2]
RESULTS_DIR = Path(__file__).resolve().parent / "results"
DEFAULT_OUT = RESULTS_DIR / "local_min.json"


class CheckError(Exception):
    """验证断言失败（负对照按预期触发也用它携带原因）。"""


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise CheckError(msg)


iv.dps = IV_DPS
_0 = iv.mpf(0)
_1 = iv.mpf(1)


# ================================================================ 二阶前向自动微分
# 三元组 (v, d1, d2) = (f, f′, f″) 的区间 enclosure；法则为精确代数：
#   (fg)′′ = f″g + 2f′g′ + fg″；(1/g)′ = −g′/g²；(1/g)″ = 2g′²/g³ − g″/g²；
#   (√a)′ = a′/(2√a)；(√a)″ = a″/(2√a) − a′²/(4·a·√a)。
# 区间求值由 mpmath.iv 的外向舍入与包含单调性给出各分量在区间上的范围 enclosure。
class D2:
    __slots__ = ("v", "d1", "d2")

    def __init__(self, v, d1, d2):
        self.v, self.d1, self.d2 = v, d1, d2


def konst(x) -> D2:
    return D2(iv.mpf(x), _0, _0)


def dvar(Z) -> D2:
    return D2(Z, _1, _0)


def dadd(a: D2, b: D2) -> D2:
    return D2(a.v + b.v, a.d1 + b.d1, a.d2 + b.d2)


def dsub(a: D2, b: D2) -> D2:
    return D2(a.v - b.v, a.d1 - b.d1, a.d2 - b.d2)


def dmul(a: D2, b: D2) -> D2:
    return D2(a.v * b.v,
              a.d1 * b.v + a.v * b.d1,
              a.d2 * b.v + 2 * (a.d1 * b.d1) + a.v * b.d2)


def dinv(a: D2) -> D2:
    b2 = a.v * a.v
    return D2(1 / a.v,
              -a.d1 / b2,
              2 * (a.d1 * a.d1) / (b2 * a.v) - a.d2 / b2)


def dsqrt(a: D2) -> D2:
    s = iv.sqrt(a.v)
    two_s = 2 * s
    return D2(s, a.d1 / two_s, a.d2 / two_s - (a.d1 * a.d1) / (4 * a.v * s))


def ddiv(a: D2, b: D2) -> D2:
    return dmul(a, dinv(b))


# ================================================================ 族能量闭式
def E_dual(Z) -> D2:
    """闭式 E(z) 及 E′、E″ 的区间 enclosure（见模块 docstring 的推导）。"""
    z = dvar(Z)
    zz = dmul(z, z)
    rho = dsqrt(dsub(konst(1), zz))                    # ρ = √(1−z²)
    one_m_zz = dsub(konst(1), zz)
    t1 = ddiv(konst(12), dsqrt(dsub(konst(2), rho)))    # 12/√(2−ρ)
    t2 = ddiv(konst(6), dsqrt(dadd(konst(2), dmul(konst(2), rho))))  # 6/√(2+2ρ)
    t3 = ddiv(konst(6), dsqrt(dmul(konst(3), one_m_zz)))  # 6/√(3(1−z²))
    t4 = ddiv(konst(3), dmul(konst(2), z))             # 3/(2z)
    t5 = dsqrt(konst(3))                               # √3（常数）
    t6 = ddiv(konst(6), dsqrt(dadd(konst(3), zz)))     # 6/√(3+z²)
    E = t1
    for t in (t2, t3, t4, t5, t6):
        E = dadd(E, t)
    return E


def E_iv(Z):
    """E(z) 的区间 enclosure（值分量）。"""
    return E_dual(Z).v


# ================================================================ 构型直接求和（定义式）
def E_direct(Z):
    """按定义直接求 E(z)：区间 z 下逐点算 9 点坐标、36 对距离、Σ 1/d。

    与闭式 E_dual 完全独立：不含任何距离分类推导；坐标用精确有理常数与 √3 表出
    （角度 2πk/3 与 π/3+2πk/3 的余弦/正弦均为 {0, ±1, ±1/2, ±√3/2}）。
    """
    Z = iv.mpf(Z)
    rho = iv.sqrt(1 - Z * Z)
    h = iv.sqrt(iv.mpf(3))
    half = iv.mpf(1) / 2
    tri = [(iv.mpf(1), _0), (iv.mpf(-1) / 2, h / 2), (iv.mpf(-1) / 2, -h / 2)]
    caps = [(half, h / 2), (iv.mpf(-1), _0), (half, -h / 2)]
    pts = ([(rho * x, rho * y, Z) for (x, y) in tri]          # 顶三角，高 +z
           + [(rho * x, rho * y, -Z) for (x, y) in tri]       # 底三角，高 −z
           + [(x, y, _0) for (x, y) in caps])                 # 赤道帽，高 0
    total = _0
    for i in range(9):
        for j in range(i + 1, 9):
            dx = pts[i][0] - pts[j][0]
            dy = pts[i][1] - pts[j][1]
            dz = pts[i][2] - pts[j][2]
            total = total + 1 / iv.sqrt(dx * dx + dy * dy + dz * dz)
    return total


# ================================================================ 区间小工具
def istr(I) -> str:
    """区间 enclosure 的完整精度字符串。"""
    return f"[{mp.nstr(mp.mpf(I.a), IV_DPS + 5)}, {mp.nstr(mp.mpf(I.b), IV_DPS + 5)}]"


def width_upper(I) -> mp.mpf:
    """区间宽度的上界（sup − inf 的外向 enclosure 的上端）。"""
    return mp.mpf((iv.mpf(I.b) - iv.mpf(I.a)).b)


def strictly_negative(I) -> bool:
    """整区间严格为负：sup < 0（端点为退化值，比较精确）。"""
    return mp.mpf(I.b) < 0


def strictly_positive(I) -> bool:
    return mp.mpf(I.a) > 0


def outward_decimal(I, k: int = 12) -> str:
    """把区间向外舍入到 k 位小数的十进制字符串（两端各多让 1 ulp_k，
    吸收端点·10^k 的 mpf 舍入，保证字符串区间 ⊇ 原区间）。"""
    lo_int = int(mp.floor(mp.mpf(I.a) * 10 ** k)) - 1
    hi_int = int(mp.ceil(mp.mpf(I.b) * 10 ** k)) + 1
    require(lo_int >= 0 and hi_int >= 0, "outward_decimal expects 0 < z* < 1")
    return f"[{lo_int // 10 ** k}.{lo_int % 10 ** k:0{k}d}, {hi_int // 10 ** k}.{hi_int % 10 ** k:0{k}d}]"


def decimal_width(s: str) -> float:
    """十进制端点字符串的精确宽度：Decimal 减法（无浮点伪精度）。

    例：端点 "0.703648376463"/"0.703649139406" 的宽度恰为 7.62943e-07；
    先前 float(hi)−float(lo) 会给出 7.629429999989057e-07 的伪精度。"""
    lo, hi = s.strip("[]").split(",")
    return float(Decimal(hi.strip()) - Decimal(lo.strip()))


def intersects(A, B) -> bool:
    return mp.mpf(A.a) <= mp.mpf(B.b) and mp.mpf(B.a) <= mp.mpf(A.b)


# ================================================================ 隔离与局部极小断言路径
def isolate(lo_s: str, hi_s: str, target_w: mp.mpf):
    """断言路径：E′ 在 [lo,hi] 两端严格变号，二分隔离至宽度 ≤ target_w。

    返回 (lo, hi, Ep_lo, Ep_hi, iterations)；任一断言失败抛 CheckError。
    负对照（--selftest）在错误区间上调用同一函数。
    """
    lo, hi = iv.mpf(lo_s), iv.mpf(hi_s)
    require(mp.mpf(lo.b) <= mp.mpf(hi.a),
            f"degenerate bracket expected: [{lo_s},{hi_s}]")
    Ep_lo, Ep_hi = E_dual(lo).d1, E_dual(hi).d1
    require(strictly_negative(Ep_lo),
            f"E'({lo_s}) must be strictly negative for a sign-change bracket, got {istr(Ep_lo)}")
    require(strictly_positive(Ep_hi),
            f"E'({hi_s}) must be strictly positive for a sign-change bracket, got {istr(Ep_hi)}")

    it = 0
    while width_upper(mpmath.mpi(lo.a, hi.b)) > target_w:
        m = (lo + hi) / 2
        Epm = E_dual(m).d1
        if strictly_negative(Epm):
            lo = m
        elif strictly_positive(Epm):
            hi = m
        else:
            raise CheckError(f"E' sign undecidable at midpoint {istr(m)}: {istr(Epm)}")
        it += 1
        require(it < 300, "bisection did not converge")
    return lo, hi, Ep_lo, Ep_hi, it


def verify_local_min(lo_s: str, hi_s: str, target_w: mp.mpf, e_star_entry=None):
    """正向验证：隔离 + E″>0 + 交叉复核 + （可选）E* 对照。返回结果字典。"""
    res = {}

    # ---- 1) z* 严格隔离
    lo, hi, Ep_lo0, Ep_hi0, it = isolate(lo_s, hi_s, target_w)
    outer = mpmath.mpi(lo.a, hi.b)                     # 外包区间 [inf lo, sup hi]
    w = width_upper(outer)
    require(w <= mp.mpf("1e-4"),
            f"isolation width {mp.nstr(w, 6)} exceeds the required 1e-4")
    Ep_lo, Ep_hi = E_dual(lo).d1, E_dual(hi).d1        # 最终端点（更紧）
    require(strictly_negative(Ep_lo),
            f"E' at final lo must stay strictly negative: {istr(Ep_lo)}")
    require(strictly_positive(Ep_hi),
            f"E' at final hi must stay strictly positive: {istr(Ep_hi)}")
    m_lo = -mp.mpf(Ep_lo.b)                            # |E′(lo)| ≥ m_lo > 0
    m_hi = mp.mpf(Ep_hi.a)                             # |E′(hi)| ≥ m_hi > 0
    require(m_lo > 0 and m_hi > 0, "|E'| lower bounds must be positive")

    # ---- 2) 族内严格局部极小：E″ 在隔离区间上整区间 > 0
    Epp = E_dual(outer).d2
    require(strictly_positive(Epp),
            f"E'' must be > 0 on the isolation interval, got {istr(Epp)}")
    # 由 E″>0 ⇒ E′ 在隔离区间上严格递增 ⇒ E′ 零点唯一、E′ 由负变正 ⇒ 严格局部极小。

    # ---- 3a) 闭式 vs 构型直接求和（定义式，独立路径）
    test_intervals = [outer,
                      mpmath.mpi(iv.mpf("0.30").a, iv.mpf("0.31").b),
                      mpmath.mpi(iv.mpf("0.50").a, iv.mpf("0.60").b),
                      mpmath.mpi(iv.mpf("0.90").a, iv.mpf("0.905").b)]
    for Zt in test_intervals:
        Ec, Ed = E_iv(Zt), E_direct(Zt)
        require(intersects(Ec, Ed),
                f"closed form {istr(Ec)} and direct configuration sum {istr(Ed)} "
                f"disjoint on {istr(Zt)}: closed form is wrong")

    # ---- 3b) MVT 一阶差商复核（在严格内点 a=sup lo、b=inf hi 上）
    a = iv.mpf(lo.b)
    b = iv.mpf(hi.a)
    require(mp.mpf(a.b) <= mp.mpf(b.a), "inner endpoints out of order")
    Ea, Eb = E_iv(a), E_iv(b)
    Q = (Eb - Ea) / (iv.mpf(b.a) - iv.mpf(a.b))        # ⊇ (E(b)−E(a))/(b−a)
    Ep_a, Ep_b = E_dual(a).d1, E_dual(b).d1
    require(mp.mpf(Q.a) > mp.mpf(Ep_a.b) and mp.mpf(Q.b) < mp.mpf(Ep_b.a),
            f"MVT difference quotient {istr(Q)} not strictly between endpoint "
            f"E' enclosures [{istr(Ep_a)}, {istr(Ep_b)}] (E''>0 ⇒ E' strictly increasing)")

    # ---- 3c) 二阶均差复核：f[a,m,b] = E″(η)/2, η ∈ (a,b)
    m = (a + b) / 2
    Em = E_iv(m)
    Q1 = (Em - Ea) / (m - a)
    Q2 = (Eb - Em) / (b - m)
    S = (Q2 - Q1) / (b - a)
    half_Epp = Epp / 2
    require(mp.mpf(S.a) >= mp.mpf(half_Epp.a) - RELAX
            and mp.mpf(S.b) <= mp.mpf(half_Epp.b) + RELAX,
            f"second divided difference {istr(S)} outside 1/2 E'' enclosure "
            f"{istr(half_Epp)} (+/- {RELAX:g})")

    # ---- 能量区间与引用常数
    Eint = E_iv(outer)
    zmid = (mp.mpf(outer.a) + mp.mpf(outer.b)) / 2
    require(abs(zmid - EXPECTED_Z) < Z_TOL,
            f"isolated z* midpoint {mp.nstr(zmid, 12)} deviates from the quoted "
            f"constant {EXPECTED_Z} by more than {Z_TOL}")

    res.update({
        "zStarInterval": outward_decimal(outer),
        "zStarIntervalWidthDecimal": decimal_width(outward_decimal(outer)),
        "zStarIntervalMpmath": istr(outer),
        "zStarMidpoint": mp.nstr(zmid, 15),
        "isolationWidthUpper": mp.nstr(w, 6),
        "bracketInitial": [lo_s, hi_s],
        "bisectionIterations": it,
        "EprimeAtLo": istr(Ep_lo),
        "EprimeAtHi": istr(Ep_hi),
        "absEprimeLowerBoundLo": mp.nstr(m_lo, 8),
        "absEprimeLowerBoundHi": mp.nstr(m_hi, 8),
        "EppOnIsolationInterval": istr(Epp),
        "uniqueCriticalPoint": True,
        "strictLocalMinInFamily": True,
        "energyInterval": istr(Eint),
    })

    # ---- 4) 族最优能量与 energies.json 的 E* 一致
    if e_star_entry is not None:
        e_star = str(e_star_entry["highPrecision"])
        Es = iv.mpf(e_star)
        dist = max(mp.mpf(Eint.a) - mp.mpf(Es.a), mp.mpf(Es.a) - mp.mpf(Eint.b))
        dist = dist if dist > 0 else mp.mpf(0)
        require(dist <= E_STAR_TOL,
                f"E(z*) enclosure {istr(Eint)} and E* = {e_star} differ by "
                f"{mp.nstr(dist, 6)} > {E_STAR_TOL:g}")
        res["eStarReference"] = {
            "source": str(Path(*ENERGIES_FILE)),
            "value": e_star_entry["value"],
            "highPrecision": e_star_entry["highPrecision"],
            "config": e_star_entry.get("config"),
            "status": e_star_entry.get("status"),
        }
        res["absEzStarMinusEstar"] = mp.nstr(dist, 6)
    return res


def load_e_star():
    p = REPO_ROOT.joinpath(*ENERGIES_FILE)
    require(p.exists(), f"missing {p} (energies.json is the E* reference)")
    with open(p) as f:
        data = json.load(f)
    require("energies" in data and "9" in data.get("energies", {}),
            f"no energies['9'] entry in {p}")
    return data["energies"]["9"]


# ================================================================ 负对照
def negative_controls(target_w: mp.mpf, e_star_entry):
    """两个负对照都必须按预期触发 CheckError，否则本函数断言失败。"""
    lo_s, hi_s = WRONG_INTERVAL
    # (i) 错误区间上的变号断言必须触发
    try:
        isolate(lo_s, hi_s, target_w)
        raise CheckError(f"negative control FAILED to trigger: E' sign-change "
                         f"assertion unexpectedly passed on [{lo_s},{hi_s}]")
    except CheckError as e:
        msg = str(e)
        require("strictly" in msg and ("negative" in msg or "positive" in msg),
                f"negative control triggered for the wrong reason: {msg}")
        ctl_interval = msg

    # (ii) 篡改 E*（+1e-3）的能量对照断言必须触发
    fake = dict(e_star_entry)
    fake["highPrecision"] = mp.nstr(mp.mpf(str(e_star_entry["highPrecision"])) + mp.mpf("1e-3"), 30)
    try:
        # 在真隔离区间上只跑能量对照路径
        lo, hi, *_ = isolate(*BRACKET, target_w)
        outer = mpmath.mpi(lo.a, hi.b)
        Eint = E_iv(outer)
        Es = iv.mpf(str(fake["highPrecision"]))
        dist = max(mp.mpf(Eint.a) - mp.mpf(Es.a), mp.mpf(Es.a) - mp.mpf(Eint.b))
        dist = dist if dist > 0 else mp.mpf(0)
        require(dist <= E_STAR_TOL,
                f"E(z*) enclosure {istr(Eint)} and E* = {fake['highPrecision']} differ by "
                f"{mp.nstr(dist, 6)} > {E_STAR_TOL:g}")
        raise CheckError("negative control FAILED to trigger: corrupted E* "
                         f"{fake['highPrecision']} unexpectedly accepted")
    except CheckError as e:
        require("differ by" in str(e),
                f"corrupted-E* control triggered for the wrong reason: {e}")
        ctl_e_star = str(e)
    return ctl_interval, ctl_e_star


# ================================================================ 主流程
def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--selftest", action="store_true",
                    help="加跑两个负对照（错误区间变号断言、篡改 E*），都按预期失败才 exit 0")
    ap.add_argument("--width", default=TARGET_WIDTH, help="隔离区间目标宽度（默认 1e-6）")
    ap.add_argument("--out", default=str(DEFAULT_OUT), help="结果 JSON 输出路径")
    args = ap.parse_args(argv)

    target_w = mp.mpf(args.width)
    e_star_entry = load_e_star()

    try:
        result = verify_local_min(BRACKET[0], BRACKET[1], target_w, e_star_entry)
        result["selftest"] = "not run (pass --selftest)"
        if args.selftest:
            ctl_interval, ctl_e_star = negative_controls(target_w, e_star_entry)
            result["selftest"] = {
                "wrongIntervalControl": {
                    "interval": list(WRONG_INTERVAL),
                    "triggered": True,
                    "message": ctl_interval,
                },
                "corruptedEStarControl": {
                    "offset": "+1e-3",
                    "triggered": True,
                    "message": ctl_e_star,
                },
            }
    except CheckError as e:
        print(f"LOCAL-MIN VERIFICATION FAILED: {e}")
        return 1

    result.update({
        "schema": "thomson-n9/bounds/local-min/1",
        "verified": True,
        "family": "triCapPrism (D3h tricapped trigonal prism), z in (0,1)",
        "closedFormE": ("12/sqrt(2-rho) + 6/sqrt(2+2*rho) + 6/sqrt(3*(1-z^2)) "
                        "+ 3/(2*z) + sqrt(3) + 6/sqrt(3+z^2),  rho = sqrt(1-z^2)"),
        "method": ("mpmath.iv interval arithmetic (dps=%d); E'/E'' by second-order "
                   "forward automatic differentiation over intervals (exact algebraic "
                   "chain rules, no hand-derived formulas); bisection on strict sign "
                   "change of E'; E''>0 on the isolation interval gives uniqueness of "
                   "the critical point and strict local minimality; cross-checks: "
                   "closed form vs direct 36-pair configuration sum (interval "
                   "intersection), MVT difference quotient vs endpoint E' enclosures, "
                   "second divided difference vs E''/2; E(z*) vs energies.json E*"
                   % IV_DPS),
        "crossChecks": {
            "closedVsDirectConfigurationSum": "interval enclosures intersect on 4 test intervals",
            "mvtDifferenceQuotient": "strictly between endpoint E' enclosures",
            "secondDividedDifference": "inside E''/2 enclosure (+/- 1e-15)",
        },
        "tolerances": {
            "isolationWidthRequired": "1e-4",
            "isolationWidthTarget": args.width,
            "eStarDistance": E_STAR_TOL,
            "ivDps": IV_DPS,
        },
        "timestamp": datetime.now(timezone.utc).isoformat(timespec="seconds"),
    })

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    with open(out, "w") as f:
        json.dump(result, f, ensure_ascii=False, indent=2, sort_keys=False)
        f.write("\n")

    print(f"z* isolation:   {result['zStarInterval']}  (width {result['zStarIntervalWidthDecimal']:.1e} decimal)")
    print(f"  mpmath:       {result['zStarIntervalMpmath']}")
    print(f"E'(lo) <= -{result['absEprimeLowerBoundLo']}   E'(hi) >= {result['absEprimeLowerBoundHi']}")
    print(f"E'' on interval: {result['EppOnIsolationInterval']}  > 0")
    print(f"E(z*) interval:  {result['energyInterval']}")
    if "absEzStarMinusEstar" in result:
        print(f"|E(z*) - E*| = {result['absEzStarMinusEstar']}  (E* = {result['eStarReference']['highPrecision']})")
    if isinstance(result["selftest"], dict):
        print("selftest: wrong-interval control triggered; corrupted-E* control triggered")
    print(f"LOCAL-MIN VERIFICATION OK  ->  {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
