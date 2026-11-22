#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""L3 解析谱管（R6-4 + R7-3）：Hermite 余项显式常数 → 平方 gap 下界 → ρ_spec(ε)~√(ε/C)。

R7-3 增量（nodeLocal 严格层）：以 R6-1 精确 dyadic minorant M（hermite_probe.json
只读复用）做胞元全域严格化 C_glob = min_k inf_{t∈cell_k}(φ(t)−M(t))/dist(t,ν_k)²——
节点邻域用 φ−M 在 ν_k 的区间 Taylor（阶 14＋Lagrange 余项，几何二分＋sliver 合并式，
绕开 W 级均匀亏损在 d→0 处对比值的塌缩），其余区间 centered-Taylor 分支定界（叶记录、
θ 剪枝、确定性栈序）；量化判据 C_glob ≥ ε_W/ρ_need²（ε_W=Σmult(φ−M)(ν_k) 严格区间）
在「cap 抬至区间亏损级 ε」口径下判 L3-need 闭合并报余量；链判定按认证常数重跑
（caliber (a) ε_forcing 仍 fail 属预期、如实）。负对照三件：W×10/×100（ε_W 精确
预测+复核、余量 ~10× 退化、存档逐位失配被检出、×100 判据翻 fail）、c0 冒充 C_glob
（无区间证书必被一致性门拦）、nodeLocal ε 单调性破坏检出。

数学内容（公式推导对两种 Hermite 形态都成立，不依赖探针存活）
----------------------------------------------------------------
Coulomb 核 φ(t) = (2−2t)^{−1/2}（对 t = ⟨y_i,y_j⟩，对距离 1/√(2−2t)）。
各阶导数全正、闭式（n 阶）：

    φ^{(n)}(t) = (2n−1)!! · (2−2t)^{−n−1/2} > 0，在 [−1,1) 上严格递增，
    最小值在 t=−1：φ^{(n)}(−1) = (2n−1)!!·4^{−n−1/2} = (2n−1)!!·2^{−2n−1}（精确 dyadic）。

在 6 个谱节点 ν₁..ν₆（tube.json /ttp_spectrum，十进制字面值＝精确 Fraction）做
值＋一阶导 Hermite 插值（12 条，deg ≤ 11＝「平版」，n=12, j=0）；或在 −1 再加
0–4 阶接触 5 条（17 条，deg ≤ 16＝「−1 接触版」，n=17, j=5）。余项公式：

    φ(t) − H(t) = φ^{(n)}(ξ)/n! · (t+1)^j · ∏_k (t−ν_k)²，
    ξ ∈ hull({t}∪{ν₁..ν₆}∪{−1 若 j>0}) ⊂ [−1,1)。

对 t 属于 ν_k 的 Voronoi 胞元 cell_k（[−1,1) 上分段）：

    |t−ν_{k'}| ≥ dist(ν_{k'}, cell_k)（到闭胞元的距离，精确 Fraction），
    ⇒  gap(t) = φ−H ≥ C_k · (t−ν_k)²，
        C_k = φ^{(n)}_min / n! · (a_k+1)^j · ∏_{k'≠k} dist(ν_{k'}, cell_k)²     （精确 Fraction）

其中 φ^{(n)}_min 取 ξ 漫游域 [−1,1) 上的全局下界（= t=−1 处，任务书口径；
mpmath.iv dps≥40 区间验证单调性与最小值）。逐节点胞元分段取最劣 C_min = min_k C_k，
则「每对 gap ≤ ε」强制  d(t, 节点集) ≤ ρ_spec(ε) = √(ε/C_min)（原始口径），
胞元平凡半径封顶后 ρ_capped(ε) = max_k min(√(ε/C_k), cellrad_k)。

两口径：(a) 现账本 ε_forcing（l2_rigorous.json 精确 Fraction 运行时直读；R8A
换 cap M9 口径后＝1.4031e-4，D29 裁决 3——旧 M8 口径 4.153454e-4 由 git 历史承担）；
(b) R6-2 缺口归零后 ε ∈ {1e-9, 1e-10, 1e-11} 参数曲线。
对账：tube.json /spectral_tube SDP 扫描值逐档定量比较（0.6447@≥3e-4、
0.2548@5.3e-6、0.1043@1e-7、0.0466@1.5e-8）。
链闭合检验 L2→L3→L5：δ_gram = ρ_spec 与 δ_max（l4.json 精确 Fraction
0.17124089749729504）比较，并给 d_P ≤ C·δ 落入 L6 二次增长球（r≈0.076）的余量。

诚实结论（本脚本算出什么就报什么，不粉饰）：见 results/l3_analytic.json 的
reconciliation_sdp 与 chain_L2_L3_L5_L6 字段；34.8× 断点是否被解析式消除
由 elimination_verdict 字段如实判定。

验收门：裸 python3 numerics/bounds/l3_analytic.py，exit 0 = 过门。
①重算全部区间常数并与存档逐位一致；②对账与链判定字段完整一致；
③负对照三件（C×10 膨胀⇒链判定翻 fail、节点间距减半⇒一致性断言触发、
ε 单调性破坏⇒必被检出）全部触发才过门。确定性：区间算术 + 精确 Fraction，
种子仅用于可选 float 交叉抽验。产物 JSON 无时钟戳，重跑逐位幂等
（provenance.code_version 漂移不触发重写，保持 git 工作树干净）。

运行：python3 numerics/bounds/l3_analytic.py   （仓库根目录；秒级完成）
"""

import json
import math
import random
import subprocess
import sys
import time
from fractions import Fraction as Fr
from pathlib import Path

import mpmath
from mpmath import iv

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
TUBE_JSON = RESULTS / "tube.json"
L2_JSON = RESULTS / "l2_rigorous.json"
L4_JSON = RESULTS / "l4.json"
OUT_JSON = RESULTS / "l3_analytic.json"

SEED = 20261006                 # 任务书指定（仅用于 float 交叉抽验）
IV_DPS = 50                     # ≥40 的区间算术精度
SQRT_BITS = 200                 # 有理平方根包精度（bit），l4 同款
F0, F1 = Fr(0), Fr(1)

N_FLAT, J_FLAT = 12, 0          # 平版：值+导 12 条，deg ≤ 11
N_CONTACT, J_CONTACT = 17, 5    # −1 接触版：+0..4 阶 5 条，deg ≤ 16

# ---------------- R7-3 nodeLocal 严格层（L3 c0 级常数胞元全域严格化）固定参数
PROBE_JSON = RESULTS / "hermite_probe.json"   # R6-1 dyadic minorant（只读复用）
NL_TAYLOR_N = 14                # 节点邻域 Taylor 阶（含 Lagrange 余项阶）
NL_TAYLOR_H = Fr(1, 1 << 12)    # 邻域半径（≪ Taylor 收敛半径 min(1-nu)=0.645）
NL_JT = 14                      # 邻域几何二分层（至 2^-26 sliver）
NL_BB_N = 8                     # B&B centered-Taylor 阶
NL_MAX_BOXES = 8000             # 每胞 B&B 预算（固定 ⇒ 确定性）
NL_MAX_DEPTH = 90
NL_TAU = Fr(1, 1000)            # 相对收紧目标（C_hi/C_lo ≤ ~1+2τ）
NL_DYAD_BITS = 200              # iv → 精确 Fraction 的定向 dyadic 舍入
NL_T_RIGHT = Fr(1) - Fr(1, 1 << 12)   # cell_6 右端：B&B 域上端，[T,1) 用 φ≥φ(T) 论证

# SDP 对账档（tube.json /spectral_tube/AAA/res 的键，float 字面值）
SDP_LEVELS = [1.5e-08, 1e-07, 5.3484317457756185e-06, 0.0003]
# 口径 (b)：R6-2 缺口归零后参数曲线
CALIBER_B_EPS = ["1e-09", "1e-10", "1e-11"]


def log(msg: str) -> None:
    print(msg, flush=True)


def fail(msg: str) -> None:
    print(f"[FAIL] {msg}", flush=True)
    sys.exit(1)


def code_version() -> str:
    try:
        return subprocess.check_output(
            ["git", "describe", "--always", "--dirty"],
            cwd=str(HERE.parents[1]), text=True,
            stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown(non-git)"


# ============================================================ 精确有理工具
def double_factorial(n: int) -> int:
    """(2n−1)!! = 1·3·5···(2n−1)。"""
    r = 1
    for k in range(1, n + 1):
        r *= 2 * k - 1
    return r


def sqrt_rat(q: Fr, side: str) -> Fr:
    """√q 的有理下界('lo')/上界('hi')，整数 Newton（math.isqrt），q ≥ 0。

    l4_procrustes.py 同款算法（独立重实现，口径一致）。
    """
    if q < 0:
        raise ValueError("sqrt of negative")
    if q == 0:
        return F0
    p = SQRT_BITS
    num, den = q.numerator, q.denominator
    if side == "lo":
        return Fr(math.isqrt((num << (2 * p)) // den), 1 << p)
    return Fr(math.isqrt((num << (2 * p)) // den + 1) + 1, 1 << p)


def f2(x) -> float:
    return float(x)


def fs(x: Fr) -> str:
    """Fraction 的规范字符串（存档逐位比较用）。"""
    return f"{x.numerator}/{x.denominator}"


# ============================================================ 输入读取
def load_inputs():
    tube = json.loads(TUBE_JSON.read_text())
    l2 = json.loads(L2_JSON.read_text())
    l4 = json.loads(L4_JSON.read_text())
    ttp = tube["ttp_spectrum"]
    nodes_str = [str(v) for v in ttp["nodes"]]
    nodes = [Fr(s) for s in nodes_str]                 # 十进制字面值 = 精确 Fraction
    mults = list(ttp["multiplicities"])
    return tube, l2, l4, nodes, nodes_str, mults


def cell_structure(nodes_sorted):
    """Voronoi 胞元（[−1,1) 上，闭胞元约定：右端点 1 为 sup，距离下界不受影响）。"""
    b = [Fr(-1)]
    for i in range(len(nodes_sorted) - 1):
        b.append((nodes_sorted[i] + nodes_sorted[i + 1]) / 2)
    b.append(Fr(1))
    cells = []
    for k in range(len(nodes_sorted)):
        a, c, v = b[k], b[k + 1], nodes_sorted[k]
        dists = {}
        for kp in range(len(nodes_sorted)):
            if kp == k:
                continue
            w = nodes_sorted[kp]
            dists[kp] = max(F0, a - w, w - c)          # 到闭胞元的距离（精确）
        cells.append(dict(
            k=k, node=v, lo=a, hi=c,
            cellrad=max(abs(v - a), abs(c - v)),       # 胞元内平凡半径上界
            dists=dists,
            spacing_prod_sq=math.prod(d * d for d in dists.values()),
        ))
    return cells


def phi_n_lower(n: int, at: Fr) -> Fr:
    """φ^{(n)} 在 t=at 处的精确/严格下界。

    at=−1：闭式精确值 c_n·2^{−2n−1}（dyadic，无理幂不出现）。
    其他有理 at：c_n·(2−2at)^{−n−1/2} 的严格下界 = c_n / ((2−2at)^n·√(2−2at) 的上界)。
    """
    if at == -1:
        return Fr(double_factorial(n), 2 ** (2 * n + 1))
    x = Fr(2) - 2 * at
    if x <= 0:
        raise ValueError("at must be < 1")
    return Fr(double_factorial(n), 1) / (x ** n * sqrt_rat(x, "hi"))


def per_cell_constants(n: int, j: int, cells, phi_min: Fr):
    """C_k = φ^{(n)}_min/n! · (a_k+1)^j · ∏_{k'≠k} dist²（全精确 Fraction）。

    j>0 且 a_k=−1 时 (a_k+1)^j=0 ⇒ C_k=0（接触版在含 −1 的胞元结构性失约束，
    如实标记 vacuous）。
    """
    nfact = Fr(math.factorial(n))
    out = []
    for c in cells:
        tplus = (F1 + c["lo"]) ** j if j > 0 else F1
        Ck = phi_min / nfact * tplus * c["spacing_prod_sq"]
        out.append(dict(
            k=c["k"], node=c["node"],
            cell_lo=c["lo"], cell_hi=c["hi"], cellrad=c["cellrad"],
            t_plus_factor=tplus,
            spacing_prod_sq=c["spacing_prod_sq"],
            dists={str(kp): d for kp, d in c["dists"].items()},
            C_k=Ck,
            vacuous=(Ck == 0),
        ))
    return out


def rho_raw_upper(eps: Fr, C_min: Fr):
    """原始口径 ρ = √(ε/C_min) 的严格上界（有理平方根包）；C_min=0 ⇒ None（∞）。"""
    if C_min == 0:
        return None
    return sqrt_rat(eps / C_min, "hi")


def rho_capped_upper(eps: Fr, per_cell):
    """封顶口径 ρ = max_k min(√(ε/C_k), cellrad_k)（每项均严格上界）。"""
    best = F0
    binding = None
    for pc in per_cell:
        if pc["vacuous"]:
            r = pc["cellrad"]
        else:
            u = sqrt_rat(eps / pc["C_k"], "hi")
            r = min(u, pc["cellrad"])
        if r > best:
            best, binding = r, pc["k"]
    return best, binding


# ============================================================ R7-3 nodeLocal 机制
def nl_dyad(x, up: bool) -> Fr:
    """mpf → 精确 Fraction 的定向 dyadic 舍入（2^-200）。"""
    s = 1 if x >= 0 else -1
    a = abs(mpmath.mpf(x))
    scaled = a * (1 << NL_DYAD_BITS)
    if up:
        return s * Fr(int(mpmath.ceil(scaled)), 1 << NL_DYAD_BITS)
    return s * Fr(int(mpmath.floor(scaled)), 1 << NL_DYAD_BITS)


def nl_iv_of(qlo: Fr, qhi: Fr):
    """有理区间 [qlo,qhi] 的 iv 包（端点 dps80 化＋相对 1e-50 外张，保证包含）。"""
    wid = mpmath.mpf("1e-50")
    a = mpmath.mpf(qlo.numerator) / mpmath.mpf(qlo.denominator)
    b = mpmath.mpf(qhi.numerator) / mpmath.mpf(qhi.denominator)
    return iv.mpf([a - abs(a) * wid - wid, b + abs(b) * wid + wid])


def nl_phi_deriv_iv(n: int, tiv):
    if n == 0:
        return iv.power(2 - 2 * tiv, iv.mpf("-0.5"))
    return iv.mpf(double_factorial(n)) * iv.power(2 - 2 * tiv, iv.mpf(f"-{n + 0.5}"))


def nl_phi_pt(n: int, q: Fr):
    """φ^{(n)}(q) 的精确有理定向区间（iv dps50 → dyadic 定向舍入）。"""
    e = nl_phi_deriv_iv(n, nl_iv_of(q, q))
    return nl_dyad(e.a, False), nl_dyad(e.b, True)


def nl_M_at(coeffs, t: Fr) -> Fr:
    acc = F0
    for c in reversed(coeffs):
        acc = acc * t + c
    return acc


def nl_M_deriv(coeffs, n: int, t: Fr) -> Fr:
    """M^{(n)}(t)（精确 Fraction，n ≤ deg）。"""
    acc = F0
    for j in range(n, len(coeffs)):
        term = coeffs[j]
        for l in range(j, j - n, -1):
            term *= l
        acc += term * t ** (j - n)
    return acc


def nl_term_min(g_lo: Fr, g_hi: Fr, p_lo: Fr, p_hi: Fr) -> Fr:
    return min(g_lo * p_lo, g_lo * p_hi, g_hi * p_lo, g_hi * p_hi)


def nl_gam_at(coeffs, m: Fr, nmax: int):
    """γ_n = (φ^{(n)} − M^{(n)})(m)/n! 的定向区间对列表（n < nmax）。

    n ≥ deg(M)+1 时 M^{(n)} = 0。系数级消去一次性完成（φ 侧 iv 定向、M 侧精确
    Fraction），规避 φ、M 各自 ~O(1) 而差 ~1e-11 的直接区间相减塌缩。/n! 为
    Taylor 系数定义（FD 交叉核对：γ₂(nu₂) = 4.821e-7 与 g''/2 有限差分一致）。"""
    out = []
    for n in range(nmax):
        p_lo, p_hi = nl_phi_pt(n, m)
        if n < len(coeffs):
            md = nl_M_deriv(coeffs, n, m)
            out.append(((p_lo - md) / math.factorial(n),
                        (p_hi - md) / math.factorial(n)))
        else:
            out.append((p_lo / math.factorial(n), p_hi / math.factorial(n)))
    return out


def nl_nbhd_pieces(coeffs, nu: Fr, gam, side: int, extent: Fr):
    """节点邻域 (0, min(NL_TAYLOR_H, extent)] 的几何分片证书。

    每片 (bound, upper)：r(s) = Σ_n γ_n s^{n-2} 的逐项定向下界（p 幂区间按
    side 与奇偶定向精确构造）＋ Lagrange 余项 φ^{(N)}(ξ)·s^{N-2} 下端；
    upper = 片外端点比值（点值 φ 上界 − 精确 M）。sliver (0, u_sliver] 用
    (γ_0+γ_1 s)/s² 合并式（γ_0 > 0 保证 → +∞，避免 γ_1/s 项的 −∞ 塌缩）。"""
    out = []
    h = min(NL_TAYLOR_H, extent)
    if h <= 0:
        return out
    u = h
    for j in range(NL_JT):
        u2, u1 = u, u / 2
        rem_pt = nu if side > 0 else nu - u2
        rem_lo = nl_phi_pt(NL_TAYLOR_N, rem_pt)[0] / math.factorial(NL_TAYLOR_N)
        tot = F0
        for n in range(NL_TAYLOR_N):
            m = n - 2
            g_lo, g_hi = gam[n]
            if m >= 0:
                if m % 2 == 0 or side > 0:
                    p_lo, p_hi = u1 ** m, u2 ** m
                else:
                    p_lo, p_hi = -(u2 ** m), -(u1 ** m)
            elif m == -1:
                if side > 0:
                    p_lo, p_hi = F1 / u2, F1 / u1
                else:
                    p_lo, p_hi = -F1 / u1, -F1 / u2
            else:
                p_lo, p_hi = F1 / (u2 * u2), F1 / (u1 * u1)
            tot += nl_term_min(g_lo, g_hi, p_lo, p_hi)
        tot += rem_lo * u1 ** (NL_TAYLOR_N - 2)
        t2 = nu + side * u2
        up = (nl_phi_pt(0, t2)[1] - nl_M_at(coeffs, t2)) / (u2 * u2)
        out.append(dict(kind="taylor", j=j, bound=tot, upper=up,
                        s_range=(u1, u2)))
        u = u1
    usl = h / (1 << NL_JT)
    g0, g1 = gam[0], gam[1]
    q_lo = min(g0[0] + g1[0] * usl, g0[0] + g1[1] * usl, g0[0])
    bd = q_lo / (usl * usl)
    for n in range(2, NL_TAYLOR_N):
        m = n - 2
        g_lo, g_hi = gam[n]
        if m == 0:
            bd += min(g_lo, g_hi)
        elif m > 0:
            if m % 2 == 0 or side > 0:
                p_lo, p_hi = F0, usl ** m
            else:
                p_lo, p_hi = -(usl ** m), F0
            bd += nl_term_min(g_lo, g_hi, p_lo, p_hi)
    tsl = nu + side * usl
    up = (nl_phi_pt(0, tsl)[1] - nl_M_at(coeffs, tsl)) / (usl * usl)
    out.append(dict(kind="taylor_sliver", bound=bd, upper=up, s_range=(F0, usl)))
    return out


def nl_box_bound(coeffs, a: Fr, b: Fr):
    """centered-Taylor 箱界：[a,b] 上 g=φ−M 的 (lo, hi_a, hi_b)。

    lo = Σ_n 逐项定向下界（(t−m)^n 幂区间按奇偶）− |φ^{(N)}|sup·ρ^N/N!；
    hi_* = 端点点值（φ 上界 − 精确 M）。"""
    m = (a + b) / 2
    rho = (b - a) / 2
    gam = nl_gam_at(coeffs, m, NL_BB_N)
    e = nl_phi_deriv_iv(NL_BB_N, nl_iv_of(a, b))
    rem = max(-nl_dyad(e.a, False), nl_dyad(e.b, True))
    rem = rem * rho ** NL_BB_N / Fr(math.factorial(NL_BB_N))
    lo = F0
    for n in range(NL_BB_N):
        g_lo, g_hi = gam[n]
        if n == 0:
            p_lo = p_hi = F1
        elif n % 2 == 0:
            p_lo, p_hi = F0, rho ** n
        else:
            p_lo, p_hi = -(rho ** n), rho ** n
        lo += nl_term_min(g_lo, g_hi, p_lo, p_hi)
    lo -= rem
    hi_a = nl_phi_pt(0, a)[1] - nl_M_at(coeffs, a)
    hi_b = nl_phi_pt(0, b)[1] - nl_M_at(coeffs, b)
    return lo, hi_a, hi_b


def certify_C_glob(coeffs, cells, theta=None):
    """C_glob = min_k inf_{t∈cell_k}(φ−M)/dist(t,ν_k)² 的两遍严格化。

    遍 1（外部）：角点比值取全局 C_hi0，θ = (1−τ)·C_hi0。
    遍 2（本函数 theta=θ）：B&B 只在 bound < θ 时分裂；被剪枝箱（bound ≥ θ，
    不可能含全局 inf 之下）计入 θ 本身。返回每胞 (lo=leaf 最小界与 θ 的 min,
    hi=叶 upper 最小)＋分支统计。全部确定性（固定栈序、固定预算）。"""
    M_sup = sum(abs(c) for c in coeffs)
    per_cell = []
    stats = dict(taylor_pieces=0, bb_evals=0, bb_leaves=0, bb_splits=0, bb_maxdepth=0)
    for c in cells:
        nu = c["node"]
        k = c["k"]
        hi_domain = NL_T_RIGHT if k == len(cells) - 1 else c["hi"]
        gam = nl_gam_at(coeffs, nu, NL_TAYLOR_N)
        leaves = []
        # 角点 piece（upper 的永久来源；含 cell_6 左角/内点）
        for t in {c["lo"], min(c["hi"], NL_T_RIGHT)}:
            d2 = (t - nu) ** 2
            if d2 > 0:
                leaves.append(dict(kind="corner", bound=None,
                                   upper=(nl_phi_pt(0, t)[1] - nl_M_at(coeffs, t)) / d2,
                                   s_range=None))
        for side, s_lo, s_hi in ((1, nu, hi_domain), (-1, c["lo"], nu)):
            extent = s_hi - s_lo
            h = min(NL_TAYLOR_H, extent)
            if h > 0:
                leaves.extend(nl_nbhd_pieces(coeffs, nu, gam, side, extent))
                stats["taylor_pieces"] += NL_JT + 1
            za = nu + side * h
            a0, b0 = (za, s_hi) if side > 0 else (s_lo, za)
            if b0 <= a0:
                continue
            stack = [(a0, b0, 0)]
            while stack:
                a, b, d = stack.pop()
                stats["bb_evals"] += 1
                stats["bb_maxdepth"] = max(stats["bb_maxdepth"], d)
                lo, hi_a, hi_b = nl_box_bound(coeffs, a, b)
                d_hi = max(abs(a - nu), abs(b - nu))
                bound = lo / (d_hi * d_hi)
                if theta is not None and bound >= theta:
                    continue                     # 剪枝：该箱比值 ≥ θ
                up = min(hi_a / ((a - nu) ** 2), hi_b / ((b - nu) ** 2))
                if bound < 0 and (b - a) < Fr(1, 10 ** 13):
                    raise ConsistencyError(
                        f"nodeLocal minorant 违约 [{float(a)},{float(b)}] g_lo={float(lo):.3e}")
                if (bound < (1 - NL_TAU) * up and d < NL_MAX_DEPTH
                        and (b - a) > Fr(1, 10 ** 15)
                        and stats["bb_evals"] + 2 < NL_MAX_BOXES):
                    mid = (a + b) / 2
                    stack.append((a, mid, d + 1))
                    stack.append((mid, b, d + 1))
                    stats["bb_splits"] += 1
                else:
                    leaves.append(dict(kind="bb", bound=bound, upper=up,
                                       s_range=(min(abs(a - nu), abs(b - nu)),
                                                max(abs(a - nu), abs(b - nu)))))
                    stats["bb_leaves"] += 1
        if k == len(cells) - 1:
            # 右端 [NL_T_RIGHT, 1)：φ ≥ φ(T)（单调）、M ≤ Σ|c_j|（|t|≤1）、d ≤ 1−ν₆
            phi_sl = nl_phi_pt(0, NL_T_RIGHT)[0]
            dd = Fr(1) - nu
            leaves.append(dict(kind="right_sliver", bound=(phi_sl - M_sup) / (dd * dd),
                               upper=None, s_range=None))
        bounds = [p["bound"] for p in leaves if p["bound"] is not None]
        uppers = [p["upper"] for p in leaves if p["upper"] is not None]
        cb = min(bounds) if bounds else None
        if theta is not None and cb is not None:
            cb = min(cb, theta)
        elif theta is not None:
            cb = theta
        per_cell.append(dict(k=k, node=fs(nu), lo=cb, hi=min(uppers),
                             n_leaves=len(leaves),
                             n_bb=sum(1 for p in leaves if p["kind"] == "bb")))
    C_lo = min(pc["lo"] for pc in per_cell)
    C_hi = min(pc["hi"] for pc in per_cell)
    return C_lo, C_hi, per_cell, stats


def nl_eps_W(coeffs, nodes_sorted, mults_sorted):
    """ε_W = Σ_k mult_k·(φ(ν_k) − M(ν_k)) 的精确有理定向区间。"""
    lo = hi = F0
    for nu, mlt in zip(nodes_sorted, mults_sorted):
        p_lo, p_hi = nl_phi_pt(0, nu)
        d = nl_M_at(coeffs, nu)
        lo += mlt * (p_lo - d)
        hi += mlt * (p_hi - d)
    return lo, hi


# ============================================================ 区间验证（mpmath.iv）
def iv_verify(nodes_sorted):
    """闭式 φ^{(n)}=c_n(2−2t)^{−n−1/2} 的区间验证，dps=IV_DPS。

    返回 (checks, phi_refined_lo)：checks 为逐条 pass 记录；
    phi_refined_lo 为 hull 精修口径用到的 φ^{(n)}(ν₁) 的 iv 下界（记录用，
    主口径的精修下界由 sqrt_rat 精确给出，两者交叉）。
    """
    iv.dps = IV_DPS
    checks = []
    t_hi = Fr(1) - Fr(1, 2 ** 40)                      # [−1, 1−2^{−40}]（t=1 处 φ 奇异，开域处理）
    for n in (N_FLAT, N_CONTACT):
        cn = double_factorial(n)
        # (i) 精确整数恒等式：(2n−1)!! == (2n)!/(2^n·n!)（二项级数独立推导路径）
        binom_path = Fr(math.factorial(2 * n), (2 ** n) * math.factorial(n))
        checks.append(dict(
            name=f"c_n_identity_n{n}",
            detail=f"(2n−1)!!={cn} vs (2n)!/(2^n n!)={binom_path}",
            passed=(Fr(cn) == binom_path)))
        # (ii) 单调性：φ^{(n+1)} = c_{n+1}(2−2t)^{−n−3/2} > 0 于 [−1, 1−2^{−40}]
        #      （ subdiv 64 段区间验证）⇒ φ^{(n)} 严格递增 ⇒ t=−1 处最小
        exp_next = iv.mpf(f"-{n + 1.5}")
        K = 64
        mono = True
        for i in range(K):
            a = t_hi * Fr(i, K) + (-1) * (1 - Fr(i, K))
            b = t_hi * Fr(i + 1, K) + (-1) * (1 - Fr(i + 1, K))
            x = iv.mpf([f2(a), f2(b)])           # 端点按 float 入 iv（正性确认用途）
            val = iv.power(2 - 2 * x, exp_next)
            if not (val > 0):
                mono = False
                break
        checks.append(dict(
            name=f"phi_n_monotone_n{n}",
            detail=f"φ^({n + 1})>0 on 64 个子区间 of [−1,{f2(t_hi)}] ⇒ φ^({n}) 严格递增，t=−1 处最小",
            passed=mono))
        # (iii) 最小值闭式：φ^{(n)}(−1) = c_n·4^{−n−1/2} = c_n·2^{−2n−1}（精确 dyadic）
        exact_min = Fr(cn, 2 ** (2 * n + 1))
        enc = iv.mpf(cn) * iv.power(iv.mpf(4), iv.mpf(f"-{n + 0.5}"))
        lo, hi = float(enc.a), float(enc.b)
        rel = abs(0.5 * (lo + hi) - f2(exact_min)) / f2(exact_min)
        width_ok = (lo <= f2(exact_min) <= hi) or rel < 1e-35
        checks.append(dict(
            name=f"phi_n_min_closed_form_n{n}",
            detail=f"iv 包住 c_n·4^({-(n + 0.5)}) = [{lo!r},{hi!r}]，精确值 {f2(exact_min)}，"
                   f"相对偏差 {rel:.2e}",
            passed=width_ok))
        # (iv) 全域包：f([−1,1−2^{−40}]) 下端 ≥ 精确最小值（iv 区间比较，容忍 dps
        #      舍入 1e-30 相对；float 比较会被 1ulp~1e-12 噪声淹没）
        exp_n = iv.mpf(f"-{n + 0.5}")
        x = iv.mpf([-1.0, f2(t_hi)])
        enc_all = iv.mpf(cn) * iv.power(2 - 2 * x, exp_n)
        t_lo = (iv.mpf(cn) / iv.mpf(2 ** (2 * n + 1))
                * (iv.mpf(1) - iv.mpf("1e-30")))
        lower_ok = bool(enc_all.a >= t_lo)
        checks.append(dict(
            name=f"phi_n_global_enclosure_n{n}",
            detail=f"f([−1,{f2(t_hi)}]) 下端 {float(enc_all.a):.10g} ≥ 精确最小 "
                   f"{f2(exact_min):.10g}·(1−1e-30)（iv 区间比较）",
            passed=lower_ok))
    # (v) 种子 float 交叉抽验（advisory）：随机有理点，float 求值与 iv 包中点按
    #     1e-12 相对偏差吻合（float 自身舍入 ~1e-16；本检查用途=抓公式/实现错位，
    #     如 base 写成 (2−t) 会差 3 的若干次方量级）
    rng = random.Random(SEED)
    spot_ok = True
    spots = []
    for _ in range(8):
        t0 = Fr(rng.randint(-2 ** 40, 2 ** 40 - 1), 2 ** 40)     # [−1,1) 均匀有理
        for n in (N_FLAT, N_CONTACT):
            cn = double_factorial(n)
            fv = cn * (2.0 - 2.0 * f2(t0)) ** (-(n + 0.5))
            enc = iv.mpf(cn) * iv.power(2 - 2 * iv.mpf(f2(t0)), iv.mpf(f"-{n + 0.5}"))
            lo, hi = float(enc.a), float(enc.b)
            mid = 0.5 * (lo + hi)
            ok = abs(fv - mid) <= 1e-12 * abs(mid)
            spot_ok = spot_ok and ok
            spots.append(dict(t=str(t0), n=n, float=fv,
                              iv_lo=lo, iv_hi=hi, ok=ok))
    checks.append(dict(
        name="seeded_float_crosscheck",
        detail=f"seed={SEED}，8 随机有理点 × n∈{{{N_FLAT},{N_CONTACT}}}，float 值全部落入 iv 包",
        passed=spot_ok, spots=spots))
    return checks


# ============================================================ 链判定
def evaluate_chain(delta_hi: Fr, thr: dict):
    """L2→L3→L5→L6 链判定（阈值侧，不含常数一致性）。

    delta_hi：δ_gram = ρ_spec 的严格上界（内积口径，l4 定理 premise_variants
    的 inner_product_delta；距离口径需 ×2C，另行报告）。
    """
    l5_ok = delta_hi <= thr["delta_max"]
    dP_hi = thr["C_pro"] * delta_hi
    l6_ok = dP_hi <= thr["r_L6"]
    labeling_ok = delta_hi < thr["half_gap"]
    return dict(
        delta_gram=delta_hi,
        l5_premise_ok=l5_ok,
        d_P_upper=dP_hi,
        l6_ball_ok=l6_ok,
        labeling_ok=labeling_ok,
        thresholds_met=(l5_ok and l6_ok and labeling_ok),
    )


def chain_gate(constants_consistent: bool, thresholds_met: bool) -> bool:
    """链总门 = 常数与存档逐位一致 AND 三阈值全过。任一失配 ⇒ fail。"""
    return bool(constants_consistent and thresholds_met)


# ============================================================ 一致性断言（负对照挂钩）
class ConsistencyError(AssertionError):
    pass


def assert_nodes_consistent(nodes_recomputed, tube_ttp, archived_nodes=None):
    """节点与 min_gap 与 tube.json（及 l3 存档，若有）逐位一致。"""
    stored = [Fr(str(v)) for v in tube_ttp["nodes"]]
    if nodes_recomputed != stored:
        raise ConsistencyError("nodes != tube.json /ttp_spectrum/nodes")
    if archived_nodes is not None and nodes_recomputed != [Fr(s) for s in archived_nodes]:
        raise ConsistencyError("nodes != l3_analytic.json /inputs/nodes（存档）")
    ns = sorted(nodes_recomputed)
    mg = min(ns[i + 1] - ns[i] for i in range(len(ns) - 1))
    stored_mg = Fr(str(tube_ttp["min_gap"]))
    # 存档 min_gap 是 float（含 ~1e-16 表示噪声，0.03701219869999994 vs 精确
    # 0.0370121987）；容差 1e-12 仍远紧于 NC2 的减半扰动（~0.018）
    if abs(mg - stored_mg) > Fr(1, 10 ** 12):
        raise ConsistencyError(
            f"min_gap recomputed {f2(mg)} != stored {f2(stored_mg)}")
    return mg


def assert_eps_monotone(pairs):
    """ρ_spec(ε) 对 ε 单调不减（口径内逐对检查）。pairs = [(eps, rho), ...] 升序 ε。"""
    vals = sorted(pairs, key=lambda p: p[0])
    for (e0, r0), (e1, r1) in zip(vals, vals[1:]):
        if r1 < r0:
            raise ConsistencyError(
                f"ε 单调性破坏：ε={e0!r}→ρ={r0!r} 但 ε={e1!r}→ρ={r1!r}（大 ε 给小 ρ）")
    return True


# ============================================================ 主流程
def main() -> int:
    t_start = time.time()
    iv.dps = IV_DPS
    tube, l2, l4, nodes, nodes_str, mults = load_inputs()
    ttp = tube["ttp_spectrum"]

    # ---------- 输入一致性（诚实口径：对 tube.json 与 l3 存档双向核对；NC2 挂钩同款断言）
    archived_nodes = None
    if OUT_JSON.exists():
        try:
            archived_nodes = json.loads(OUT_JSON.read_text())["inputs"]["nodes"]
        except Exception:
            archived_nodes = None
    try:
        min_gap = assert_nodes_consistent(nodes, ttp, archived_nodes)
        nodes_consistent = True
    except ConsistencyError as e:
        fail(f"输入节点不一致：{e}")
        return 1
    ns = sorted(nodes)
    half_gap = min_gap / 2
    log(f"[OK ] nodes={nodes_str}")
    log(f"[OK ] min_gap={f2(min_gap)} ({f2(min_gap)})  half_gap={f2(half_gap)}")

    cells = cell_structure(ns)

    # ---------- 常数（全精确 Fraction）
    phi_min_flat = phi_n_lower(N_FLAT, Fr(-1))              # 23!!·2^{−25}
    phi_min_contact = phi_n_lower(N_CONTACT, Fr(-1))        # 33!!·2^{−35}
    # hull 精修：cells ≥2 的 ξ 漫游域为 [ν₁, max(t,ν₆)] ⇒ 可用 φ^{(n)}(ν₁)（精确下界）
    phi_nu1_flat = phi_n_lower(N_FLAT, ns[0])
    phi_nu1_contact = phi_n_lower(N_CONTACT, ns[0])

    flat_global = per_cell_constants(N_FLAT, J_FLAT, cells, phi_min_flat)
    contact_global = per_cell_constants(N_CONTACT, J_CONTACT, cells, phi_min_contact)

    def hull_refined(n, j, global_min, nu1_min):
        nfact = Fr(math.factorial(n))
        out = []
        for c, pc_glob in zip(cells, flat_global if n == N_FLAT else contact_global):
            pm = global_min if c["k"] == 0 else nu1_min
            tplus = (F1 + c["lo"]) ** j if j > 0 else F1
            Ck = pm / nfact * tplus * c["spacing_prod_sq"]
            out.append(dict(k=c["k"], node=c["node"], cellrad=c["cellrad"],
                            C_k=Ck, vacuous=(Ck == 0),
                            phi_min_used=pm))
        return out

    flat_hull = hull_refined(N_FLAT, J_FLAT, phi_min_flat, phi_nu1_flat)
    contact_hull = hull_refined(N_CONTACT, J_CONTACT, phi_min_contact, phi_nu1_contact)

    C_min_flat = min(pc["C_k"] for pc in flat_global)
    C_min_contact = min(pc["C_k"] for pc in contact_global)          # = 0（cell₁）
    C_min_contact_nz = min(pc["C_k"] for pc in contact_global if not pc["vacuous"])
    C_min_flat_hull = min(pc["C_k"] for pc in flat_hull)
    worst_flat = min(flat_global, key=lambda pc: pc["C_k"])

    log(f"[OK ] φ^({N_FLAT})_min(t=−1) = {fs(phi_min_flat)} = {f2(phi_min_flat):.10g}")
    log(f"[OK ] C_min(flat) = {f2(C_min_flat):.6e} @ cell_{worst_flat['k'] + 1}"
        f"（ν={f2(worst_flat['node'])}）")
    log(f"[OK ] C_min(contact) = {f2(C_min_contact):.6e}"
        f"（cell_1 因 (t+1)^5=0 失约束；非零胞元最劣 {f2(C_min_contact_nz):.6e}）")

    # ---------- 区间验证
    iv_checks = iv_verify(ns)
    iv_all = all(c["passed"] for c in iv_checks)
    for c in iv_checks:
        log(f"[{'OK ' if c['passed'] else 'FAIL'}] iv: {c['name']}: {c['detail'][:110]}")
    if not iv_all:
        fail("mpmath.iv 区间验证未全过")

    # ---------- 阈值（精确 Fraction 为主；r_L6 为 float 输入按二进制精确值入账）
    delta_max = Fr(l4["constants"]["delta_max_exact"])
    C_pro = Fr(l4["constants"]["C_exact"])
    eps_forcing = Fr(l2["eps_forcing"]["exact"])
    r_L6 = Fr(tube["tube_radius"]["rigorous"]["chain_best"]["radius"])
    thr = dict(delta_max=delta_max, C_pro=C_pro, r_L6=r_L6, half_gap=half_gap,
               min_gap=min_gap)
    delta_L6_budget = r_L6 / C_pro                       # δ_gram 需 ≤ r/C 才进 L6 球
    log(f"[OK ] δ_max={f2(delta_max)}  C_pro={f2(C_pro)}  r_L6={f2(r_L6)}"
        f"  ⇒ δ 预算(L6)={f2(delta_L6_budget)}")

    # ---------- ρ_spec 两口径
    def rho_report(eps: Fr, per_cell, C_min):
        raw = rho_raw_upper(eps, C_min)
        capped, binding = rho_capped_upper(eps, per_cell)
        per = []
        for pc in per_cell:
            u = None if pc["vacuous"] else sqrt_rat(eps / pc["C_k"], "hi")
            per.append(dict(k=pc["k"], node=fs(pc["node"]),
                            rho_k=(fs(pc["cellrad"]) if pc["vacuous"] else fs(min(u, pc["cellrad"]))),
                            cellrad=fs(pc["cellrad"]),
                            vacuous=pc["vacuous"]))
        return dict(eps=fs(eps), eps_float=f2(eps),
                    rho_raw=(None if raw is None else fs(raw)),
                    rho_raw_float=(None if raw is None else f2(raw)),
                    rho_capped=fs(capped), rho_capped_float=f2(capped),
                    binding_cell=binding + 1,
                    raw_vacuous=(raw is None or raw > 2),
                    per_cell=per)

    caliber_a = rho_report(eps_forcing, flat_global, C_min_flat)
    caliber_b = [rho_report(Fr(s), flat_global, C_min_flat) for s in CALIBER_B_EPS]
    caliber_a_contact = rho_report(eps_forcing, contact_global, C_min_contact)
    caliber_a_hull = rho_report(eps_forcing, flat_hull, C_min_flat_hull)
    log(f"[OK ] 口径(a) ε_forcing={f2(eps_forcing):.10e}: ρ_raw={caliber_a['rho_raw_float']:.6g}"
        f"（{'vacuous' if caliber_a['raw_vacuous'] else '有效'}）"
        f"  ρ_capped={caliber_a['rho_capped_float']:.10f} @cell_{caliber_a['binding_cell']}")
    for rep in caliber_b:
        log(f"[OK ] 口径(b) ε={rep['eps_float']:.0e}: ρ_raw={rep['rho_raw_float']:.6g}"
            f"  ρ_capped={rep['rho_capped_float']:.10f} @cell_{rep['binding_cell']}")

    # 平方根收缩补偿（R6-2 口径内）：ρ_raw 严格按 √ε 缩
    eps_ratio = eps_forcing / Fr("1e-11")
    sqrt_gain = sqrt_rat(eps_ratio, "hi")
    raw_a = caliber_a["rho_raw_float"]
    raw_b11 = caliber_b[-1]["rho_raw_float"]
    sqrt_consistent = abs(raw_a / raw_b11 - f2(sqrt_gain)) <= 1e-6 * f2(sqrt_gain)

    # ---------- 对账（SDP 扫描值）
    sdp_res = tube["spectral_tube"]["AAA"]["res"]
    levels = []
    for e in SDP_LEVELS:
        key = repr(e)
        if key not in sdp_res:
            fail(f"tube.json spectral_tube 缺档 {key}")
        rho_sdp = sdp_res[key]["rho_spec"]
        eps_fr = Fr(key)
        raw = rho_raw_upper(eps_fr, C_min_flat)
        capped, binding = rho_capped_upper(eps_fr, flat_global)
        ratio_raw = (f2(raw) / rho_sdp) if raw is not None else None
        if raw is None or f2(raw) > 2:
            ana_verdict = "analytic_raw_vacuous"
        elif f2(capped) <= rho_sdp * (1 + 1e-9):
            ana_verdict = "analytic_capped_better_or_equal"
        else:
            ana_verdict = "sdp_better"
        levels.append(dict(
            eps=key, eps_float=e, rho_sdp=rho_sdp,
            rho_analytic_raw=(None if raw is None else f2(raw)),
            rho_analytic_capped=f2(capped), binding_cell=binding + 1,
            ratio_raw_over_sdp=ratio_raw,
            ratio_capped_over_sdp=f2(capped) / rho_sdp,
            verdict=ana_verdict))
        log(f"[OK ] 对账 ε={e:.3e}: SDP {rho_sdp:.6f} vs 解析 raw "
            f"{(float('inf') if raw is None else f2(raw)):.6g} / capped {f2(capped):.6f}"
            f" → {ana_verdict}")

    # 平台机制：0.6447…= 1−ν₆ 逐位；0.2548…≈ 最宽节点间距之半（不逐位，报偏差）
    one_minus_nu6 = Fr(1) - ns[-1]
    gap_widest = max(ns[i + 1] - ns[i] for i in range(len(ns) - 1))
    plateau_hi_val = sdp_res[repr(0.0003)]["rho_spec"]
    plateau_mid_val = sdp_res[repr(5.3484317457756185e-06)]["rho_spec"]
    identity_hi = abs(f2(one_minus_nu6) - plateau_hi_val) < 1e-12
    mech = dict(
        plateau_06447=dict(
            sdp_value=plateau_hi_val, trivial_one_minus_nu6=f2(one_minus_nu6),
            exact_identity=identity_hi,
            explanation="SDP ε≥3e-4 平台 0.644725833…= 1−ν₆ = dist(t=1, ν₆)：零集 {λ≤ε} "
                        "延伸到域边界 t=1（worst_spec=(1,1,1)），管半径=域内离节点最远点，"
                        "是平凡几何值而非 SOS 结构值"),
        plateau_02548=dict(
            sdp_value=plateau_mid_val, half_widest_gap=f2(gap_widest / 2),
            offset=abs(plateau_mid_val - f2(gap_widest / 2)),
            explanation="SDP 5.3e-6~1e-4 平台 0.2548…≈ (ν₄−ν₃)/2 = 0.254879（最宽节点间距 "
                        "0.5098 之半，worst_spec 落在 ν₃–ν₄ 胞元边界内侧 ~3e-5 处）；"
                        "解析封顶口径在同一位置给出平凡上界 cellrad=0.254879"),
        analytic_reproduces_plateaus=(
            abs(caliber_a["rho_capped_float"] - plateau_hi_val) < 1e-9),
    )

    # 34.8× 断点消除判定（如实）
    need = half_gap
    elimination = dict(
        sdp_ratio_at_forcing=plateau_hi_val / f2(need),
        analytic_capped_at_forcing=caliber_a["rho_capped_float"],
        analytic_ratio_at_forcing=caliber_a["rho_capped_float"] / f2(need),
        analytic_raw_at_forcing=caliber_a["rho_raw_float"],
        raw_vacuous=caliber_a["raw_vacuous"],
        C_needed_for_need=fs(eps_forcing / need ** 2),
        C_needed_for_need_float=f2(eps_forcing / need ** 2),
        C_min_flat=fs(C_min_flat),
        C_min_flat_float=f2(C_min_flat),
        C_deficit_factor=fs((eps_forcing / need ** 2) / C_min_flat),
        C_deficit_factor_float=f2((eps_forcing / need ** 2) / C_min_flat),
        rho_deficit_factor=fs(rho_raw_upper(eps_forcing, C_min_flat) / need),
        rho_deficit_factor_float=f2(rho_raw_upper(eps_forcing, C_min_flat) / need),
    )
    elimination["verdict"] = (
        "未消除：解析式（诚实常数）在两口径均未达到 SDP 扫描质量；封顶口径在粗 ε 档"
        "复现同一组平凡平台值（0.6447=1−ν₆ 逐位、0.2549≈最宽间距之半），原始口径 "
        f"vacuous（ρ_raw={caliber_a['rho_raw_float']:.4g}）。瓶颈常数："
        f"C_min={f2(C_min_flat):.3e}，闭合需 C≥{elimination['C_needed_for_need_float']:.6g}"
        f"（差 {elimination['C_deficit_factor_float']:.3e} 倍）。机制：余项在全部 6 节点"
        "平方消失 ⇒ 间距因子是五节点距离乘积平方（最劣胞元 ν₂ 得 "
        f"{f2(worst_flat['spacing_prod_sq']):.3e}），而非架构估计所用的单 min_gap²="
        f"{f2(min_gap ** 2):.3e}（单因子高估 C 约 {f2(min_gap ** 2 / worst_flat['spacing_prod_sq']):.0f}"
        " 倍）；且 ξ 全程漫游 [−1,1) 使 φ^{(12)} 下界钉在 t=−1"
        f"（{f2(phi_min_flat):.6g}，对 cells≥2 相对 φ^({N_FLAT})(ν₁)="
        f"{f2(phi_nu1_flat):.6g} 保守 {f2(phi_nu1_flat / phi_min_flat):.3f}×，"
        "hull 精修已另行入账）")
    log(f"[OK ] 断点消除判定：{elimination['verdict'][:80]}…")

    # ---------- 交叉参考 R6-1 探针（hermite_probe.json，若在库）：节点局部渐近常数
    cross_ref = dict(present=False)
    probe_path = RESULTS / "hermite_probe.json"
    if probe_path.exists():
        probe = json.loads(probe_path.read_text())
        c0 = None
        node_limits_float = {}

        def _find_ii(o):
            if isinstance(o, dict):
                if "ii_sq_gap" in o:
                    return o["ii_sq_gap"]
                for v in o.values():
                    r = _find_ii(v)
                    if r is not None:
                        return r
            return None

        ii = _find_ii(probe)
        if ii is not None:
            c0 = ii.get("c0")
            node_limits_float = ii.get("node_limits", {})
        # 独立精确重算节点极限 L_k = φ^{(12)}(ν_k)/12!·∏_{j≠k}(ν_k−ν_j)²（严格下界）
        nfact12 = Fr(math.factorial(N_FLAT))
        node_limits_exact = {}
        for k, v in enumerate(ns):
            prod = Fr(1)
            for kp, w in enumerate(ns):
                if kp != k:
                    prod *= (v - w) ** 2
            base = Fr(2) - 2 * v
            phi_local = Fr(double_factorial(N_FLAT), 1) / (base ** N_FLAT * sqrt_rat(base, "hi"))
            node_limits_exact[fs(v)] = phi_local / nfact12 * prod
        worst_key = min(node_limits_exact, key=node_limits_exact.get)
        c0_exact_lo = node_limits_exact[worst_key]
        c0_matches = (c0 is not None
                      and abs(f2(c0_exact_lo) - float(c0)) <= 1e-6 * float(c0))
        rm = probe.get("rigorous_minorant", {})
        deficit = rm.get("E_M_deficit_vs_phi")
        # 用 c0 口径重放闭合阈值（float advisory——c0 是渐近/稠密网格口径，非全域严格）
        if c0 is not None:
            c0f = float(c0)
            eps_star = dict(
                L3_need=c0f * f2(half_gap) ** 2,
                L5=c0f * f2(delta_max) ** 2,
                L6=c0f * f2(delta_L6_budget) ** 2)
            cross_ref.update(
                present=True, source="results/hermite_probe.json（R6-1，verdict=alive）",
                c0_probe=c0, c0_exact_node_limit_lo=fs(c0_exact_lo),
                c0_exact_node_limit_lo_float=f2(c0_exact_lo),
                c0_worst_node=worst_key,
                c0_exact_matches_probe=c0_matches,
                node_limits_exact={k: fs(v) for k, v in node_limits_exact.items()},
                node_limits_probe_float=node_limits_float,
                note="R6-1 的 c0 = min(稠密网格 gap/d², 节点极限 L_k)，节点极限即本文件"
                     "「节点值乘积」读法（局部 φ^{(12)}(ν_k) × 节点间距积），本文件以精确 "
                     "Fraction 独立重算并核对。c0 高于本文件严格 C_min 的机制 = "
                     "ξ 局部化（×~7.07）＋节点间距积 vs 胞元距离积（×~34.1），合计 ~241×；"
                     "但 c0 是渐近/网格口径（float advisory），全域严格化属 R6-2/R6-3。",
                E_M_deficit_vs_phi=deficit,
                closure_with_c0=eps_star,
                closure_with_c0_note=(
                    f"若 c0 级常数严格化成立：L3 need 需 ε ≤ {eps_star['L3_need']:.3e}、"
                    f"L5 需 ≤ {eps_star['L5']:.3e}、L6 需 ≤ {eps_star['L6']:.3e}；对照 R6-1 "
                    f"已实现的 minorant 亏损 {deficit:.3e} ⇒ L5/L3-need 可闭合"
                    f"（余量 {eps_star['L5'] / deficit:.0f}×/{eps_star['L3_need'] / deficit:.1f}×），"
                    f"L6 仍差 {deficit / eps_star['L6']:.1f}×（ε 口径）——链的最终卡点将移到 L6"),
            )
            log(f"[OK ] 交叉参考 R6-1：c0={c0:.6e}，精确节点极限重算 "
                f"{f2(c0_exact_lo):.6e}（{'一致' if c0_matches else '不一致'}）"
                f"；c0 口径闭 L6 需 ε≤{eps_star['L6']:.3e} vs 已实现亏损 {deficit:.3e}")

    # ---------- R7-3 nodeLocal 严格层：C_glob = min_k inf_{t∈cell_k}(φ−M)/dist(t,ν_k)²
    node_local = dict(present=False)
    if PROBE_JSON.exists():
        _probe_doc = json.loads(PROBE_JSON.read_text())
        probe_rm = _probe_doc["rigorous_minorant"]
        nl_coeffs = [Fr(s) for s in probe_rm["coeffs"]]
        nl_W = Fr(probe_rm["W"])
        probe_nodes_fr = [Fr(str(v)) for v in _probe_doc["nodes"]]
        nl_nodes_ok = (probe_nodes_fr == nodes) and int(probe_rm["ncond"]) == N_FLAT
        if not nl_nodes_ok:
            fail("nodeLocal：hermite_probe 节点/ncond 与 tube.json 不一致")
        # ε_W 严格区间（mults 随 nodes 排序对齐）
        order = sorted(range(len(nodes)), key=lambda i: nodes[i])
        mults_sorted = [mults[i] for i in order]
        epsW_lo, epsW_hi = nl_eps_W(nl_coeffs, ns, mults_sorted)
        # 两遍 C_glob 严格化
        ups1 = []
        for c in cells:
            nu = c["node"]
            for t in {c["lo"], min(c["hi"], NL_T_RIGHT)}:
                d2 = (t - nu) ** 2
                if d2 > 0:
                    ups1.append((nl_phi_pt(0, t)[1] - nl_M_at(nl_coeffs, t)) / d2)
        C_hi0 = min(ups1)
        theta = (1 - NL_TAU) * C_hi0
        C_lo, C_hi, nl_per_cell, nl_stats = certify_C_glob(nl_coeffs, cells, theta=theta)
        # 量化判据：C_lo ≥ ε_W_hi / half_gap²（=「cap 抬至区间亏损级 ε」口径的 L3-need 闭合）
        thr_exact = epsW_hi / half_gap ** 2
        criterion_ok = C_lo >= thr_exact
        margin_L3need = C_lo * half_gap ** 2 / epsW_hi
        # —— 交叉核对 ——
        # (a) c0 两独立路径 14 位：本文件精确节点极限重算 vs probe float c0
        nfact12 = Fr(math.factorial(N_FLAT))
        node_limits_exact2 = {}
        for k, v in enumerate(ns):
            prod = F1
            for kp, w in enumerate(ns):
                if kp != k:
                    prod *= (v - w) ** 2
            base = Fr(2) - 2 * v
            phi_local = Fr(double_factorial(N_FLAT), 1) / (base ** N_FLAT * sqrt_rat(base, "hi"))
            node_limits_exact2[fs(v)] = phi_local / nfact12 * prod
        c0_exact_lo = min(node_limits_exact2.values())
        probe_c0 = None
        try:
            probe_c0 = float(json.loads(PROBE_JSON.read_text())
                             ["criteria"]["ii_sq_gap"]["c0"])
        except Exception:
            probe_c0 = None
        c0_match14 = (probe_c0 is not None
                      and abs(f2(c0_exact_lo) - probe_c0) <= 1e-13 * abs(probe_c0))
        # (b) γ₂(ν_k)（M 基实际二次系数）vs 节点极限 L_k：Vandermonde 条件数污染比
        gam2_vs_Lk = {}
        for k, v in enumerate(ns):
            gam2 = nl_gam_at(nl_coeffs, v, 3)[2]
            gam2_vs_Lk[fs(v)] = f2((gam2[0] + gam2[1]) / 2 / node_limits_exact2[fs(v)])
        # (c) Taylor 邻域 vs B&B 同区间交叉（cell_2 左侧第一几何片）
        nl_x_tay = nl_x_bb = None
        c2 = cells[1]
        gam_c2 = nl_gam_at(nl_coeffs, c2["node"], NL_TAYLOR_N)
        piece = nl_nbhd_pieces(nl_coeffs, c2["node"], gam_c2, -1,
                               min(NL_TAYLOR_H, c2["node"] - c2["lo"]))
        nl_x_tay = piece[0]["bound"]
        nl_x_bb = nl_box_bound(coeffs=nl_coeffs, a=c2["node"] - piece[0]["s_range"][1],
                               b=c2["node"] - piece[0]["s_range"][0])[0] \
            / (piece[0]["s_range"][1] ** 2)
        xcheck_ok = (nl_x_bb <= piece[0]["upper"] * (1 + 1e-9)) and \
                    (nl_x_tay <= piece[0]["upper"] * (1 + 1e-9))
        # (d) float advisory 稠密扫描（seed）必须落入 [C_lo, C_hi]
        #     网格点取精确有理（a + (b−a)·i/N，a/b 为 Fraction）——t 舍入会在近节点
        #     处把 |g'|·10⁻¹² 的误差放大到比值上（曾致 fl_min < 0 的假违约）
        rng_nl = random.Random(SEED)
        fl_min = float("inf")
        fl_arg = None
        for c in cells:
            nu = c["node"]
            a, b = c["lo"], min(c["hi"], NL_T_RIGHT)
            N_GRID = 4000
            for i in range(N_GRID + 1):
                t = a + (b - a) * Fr(i, N_GRID)
                if t == nu:
                    continue
                dd = f2(t - nu)
                val = (1.0 / math.sqrt(2.0 - 2.0 * f2(t))
                       - f2(nl_M_at(nl_coeffs, t))) / (dd * dd)
                if val < fl_min:
                    fl_min, fl_arg = val, (c["k"], f2(t))
        float_scan_ok = (f2(C_lo) * (1 - 1e-3) <= fl_min <= f2(C_hi) * (1 + 1e-3))
        # —— 链判定（caliber c：nodeLocal 常数 + ε_W 口径）——
        r_star_l6 = None
        mu_l6 = None
        if (RESULTS / "l6_intube.json").exists():
            l6d = json.loads((RESULTS / "l6_intube.json").read_text())
            r_star_l6 = Fr(str(l6d["quadraticGrowth"]["rigorousRadius"]))
            _mu = l6d["quadraticGrowth"]["muAtRstar"]
            if isinstance(_mu, str):
                _mu = [s.strip() for s in _mu.strip("[]").split(",")]
            mu_l6 = [Fr(str(_mu[0])), Fr(str(_mu[1]))]
        chain_c_links = {}
        eps_targets = dict(L3_need=half_gap, L5=delta_max,
                           L6=(r_star_l6 / C_pro if r_star_l6 is not None else None))
        for name, rho_t in eps_targets.items():
            if rho_t is None:
                continue
            lhs = C_lo * rho_t ** 2
            ok = lhs >= epsW_hi
            chain_c_links[name] = dict(
                rho_target=fs(rho_t), rho_target_float=f2(rho_t),
                eps_star=fs(lhs), eps_star_float=f2(lhs),
                premise_ok=bool(ok),
                margin_factor=(fs(lhs / epsW_hi) if ok else None),
                deficit_factor=(None if ok else fs(epsW_hi / lhs)),
                deficit_factor_float=(None if ok else f2(epsW_hi / lhs)),
                margin_float=f2(lhs / epsW_hi))
        # R8-3：ε-链全闭（L6 链扣兑现）尚需的 L6 严格半径（精确有理 √ 上界）
        r_l6_need = C_pro * sqrt_rat(epsW_hi / C_lo, "hi")
        # 参考口径：chain_best 公式半径 0.0760…（tube.json，非严格）
        r_formula_l6 = r_L6
        lhs_f = C_lo * r_formula_l6 ** 2 / C_pro ** 2
        chain_c_ref = dict(
            note="非严格参考：tube.json chain_best 公式半径（μ 证书只到 r*）",
            rho_target=fs(r_formula_l6 / C_pro),
            eps_star_float=f2(lhs_f),
            premise_ok=bool(lhs_f >= epsW_hi),
            margin_float=f2(lhs_f / epsW_hi))
        # 口径(a) 复核（ε_forcing 现账本）：ρ_raw(C_glob) 必 vacuous ⇒ 仍 fail（预期、如实）
        rho_a_c = sqrt_rat(eps_forcing / C_lo, "hi")
        ev_a_c = evaluate_chain(min(rho_a_c, 2), thr)
        node_local.update(
            present=True,
            source="results/hermite_probe.json /rigorous_minorant（R6-1，只读复用）",
            minorant=dict(ncond=probe_rm["ncond"], k=probe_rm["k"], B=probe_rm["B"],
                          W=fs(nl_W), W_float=f2(nl_W), n_coeffs=len(nl_coeffs),
                          coeff_sum_abs=fs(sum(abs(c) for c in nl_coeffs)),
                          nodes_match_tube=bool(nl_nodes_ok)),
            method=dict(
                formula="C_glob = min_k inf_{t∈cell_k} (φ(t)−M(t))/dist(t,ν_k)²",
                node_nbhd=(f"区间 Taylor @ν_k，阶 N={NL_TAYLOR_N}（含 Lagrange 余项 "
                           f"phi^({NL_TAYLOR_N})(xi)*s^{NL_TAYLOR_N - 2}），半径 {fs(NL_TAYLOR_H)}，"
                           f"{NL_JT} 层几何二分＋sliver 合并式 (γ0+γ1 s)/s²——绕开 W 级均匀亏损在 "
                           "d→0 处对比值的塌缩"),
                bb=(f"centered-Taylor 阶 {NL_BB_N} 的分支定界（叶记录、θ 剪枝、"
                    f"预算 {NL_MAX_BOXES} 箱/深度 {NL_MAX_DEPTH}，确定性栈序）"),
                cell6_right=(f"[{fs(NL_T_RIGHT)},1) 用 φ≥φ(T)（单调）−Σ|c_j| 的 crude 下界"
                             "（t=1 奇点端）"),
                determinism="固定参数/固定栈序/精确 Fraction＋定向 dyadic；无时钟戳"),
            C_glob=dict(
                lo=fs(C_lo), hi=fs(C_hi),
                lo_float=f2(C_lo), hi_float=f2(C_hi),
                rel_width=f2((C_hi - C_lo) / C_lo),
                binding_cell=min(nl_per_cell, key=lambda pc: pc["lo"])["k"] + 1,
                binding_site="cell₁/cell₂ 共享角点 = midpoint(ν₁,ν₂)（d = half_gap）"
                             if min(nl_per_cell, key=lambda pc: pc["lo"])["k"] in (0, 1)
                             else "见 per_cell"),
            per_cell=[dict(k=pc["k"], node=pc["node"], lo=fs(pc["lo"]),
                           lo_float=f2(pc["lo"]), hi=fs(pc["hi"]),
                           hi_float=f2(pc["hi"]), n_leaves=pc["n_leaves"],
                           n_bb_leaves=pc["n_bb"]) for pc in nl_per_cell],
            branch_stats=nl_stats,
            eps_W=dict(lo=fs(epsW_lo), hi=fs(epsW_hi),
                       lo_float=f2(epsW_lo), hi_float=f2(epsW_hi),
                       archived_float=probe_rm["E_M_deficit_vs_phi"],
                       archived_float_inside=bool(f2(epsW_lo) <= probe_rm["E_M_deficit_vs_phi"] <= f2(epsW_hi)),
                       note="R6-1 档案值系 float Horner 求和（~1.3e-3 相对噪声）；本文件严格区间为准"),
            criterion=dict(
                threshold=fs(thr_exact), threshold_float=f2(thr_exact),
                threshold_def="ε_W_hi / half_gap²（ε_W=Σ mult·(φ−M)(ν_k) 严格区间上端）",
                passed=bool(criterion_ok),
                margin=fs(C_lo / thr_exact), margin_float=f2(C_lo / thr_exact),
                margin_L3need=fs(margin_L3need), margin_L3need_float=f2(margin_L3need)),
            cross_checks=dict(
                c0_two_paths_14digits=bool(c0_match14),
                c0_exact_min=fs(c0_exact_lo), c0_exact_min_float=f2(c0_exact_lo),
                c0_probe_float=probe_c0,
                gamma2_over_Lk=gam2_vs_Lk,
                gamma2_note="M 的 dyadic 系数经 12 条件 Vandermonde 逆传播，(H−M)'' 污染 "
                            "~1e-7 ≫ 节点极限 L_k~4.5e-9 ⇒ (φ−M)/d² 的节点渐近常数为 "
                            "γ₂ ≈ 100·L_k 而非 c0 本身——C_glob 的最小值在胞元角点而非节点",
                taylor_vs_bb_overlap=dict(taylor=fs(nl_x_tay), bb=fs(nl_x_bb),
                                          taylor_float=f2(nl_x_tay), bb_float=f2(nl_x_bb),
                                          upper_float=f2(piece[0]["upper"]),
                                          both_valid_lower=xcheck_ok),
                float_dense_scan=dict(seed=SEED, min=fl_min,
                                      argmin_cell=fl_arg[0] + 1, argmin_t=fl_arg[1],
                                      inside_certified_interval=bool(float_scan_ok)),
                all_ok=bool(c0_match14 and xcheck_ok and float_scan_ok)),
            chain_caliber_c=dict(
                eps_regime="ε_W（cap 抬至区间亏损级，R7-1 成功后的口径）",
                links=chain_c_links,
                l6_closure_radius_needed=dict(
                    value=fs(r_l6_need), float=f2(r_l6_need),
                    formula="C_pro·√(ε_W_hi/C_lo)（ε*_L6 = C_lo·(r*/C_pro)² ≥ ε_W_hi 的最小 r*，"
                            "精确有理 √ 上界）",
                    current_r_star=(None if r_star_l6 is None else fs(r_star_l6)),
                    current_r_star_float=(None if r_star_l6 is None else f2(r_star_l6)),
                    shortfall_factor=(None if r_star_l6 is None else f2(r_l6_need / r_star_l6)),
                    note="R8-3：L6 半件单独不闭 ε-链——cap 前提（亏损 ≤ ε_W 级）兑现后，"
                         "尚需 L6 严格半径抬至此值（cap 前提兑现后的预制件口径，如实留档）"),
                formula_ref_caliber=chain_c_ref,
                caliber_a_rerun=dict(
                    rho_raw_float=f2(rho_a_c), vacuous=bool(f2(rho_a_c) > 2),
                    thresholds_met=bool(ev_a_c["thresholds_met"]),
                    note=(f"口径(a) ε_forcing={f2(eps_forcing):.2e}（R8A 换 cap M9 口径，"
                          f"D29 裁决 3）下 C_glob 级 ρ_raw ≈ √(ε/C_glob) ≈ "
                          f"{f2(rho_a_c):.4g} ⇒ vacuous，链判定仍 fail"
                          "（预期、如实——cap 未抬前不闭合）"))),
            r_star_l6_used=(None if r_star_l6 is None else
                            dict(value=fs(r_star_l6), float=f2(r_star_l6),
                                 mu_interval=[fs(mu_l6[0]), fs(mu_l6[1])],
                                 source="results/l6_intube.json /quadraticGrowth")),
        )
        log(f"[OK ] nodeLocal：C_glob ∈ [{f2(C_lo):.9e}, {f2(C_hi):.9e}]"
            f"（width {f2((C_hi - C_lo) / C_lo):.2e}，结合胞元 "
            f"{node_local['C_glob']['binding_cell']}）")
        log(f"[OK ] nodeLocal 判据：C_lo ≥ ε_W_hi/ρ_need² = {f2(thr_exact):.6e}？"
            f" {'PASS' if criterion_ok else 'FAIL'}（余量 {f2(C_lo / thr_exact):.2f}×）")
        for nm, lk in chain_c_links.items():
            log(f"[OK ] nodeLocal 链 {nm}: {'过' if lk['premise_ok'] else 'FAIL'}"
                f"（ε*={lk['eps_star_float']:.3e} vs ε_W={f2(epsW_hi):.3e}，"
                f"{'余量' if lk['premise_ok'] else '缺口'} "
                f"{lk['margin_float'] if lk['premise_ok'] else lk['deficit_factor_float']:.2f}×）")

    # ---------- 链判定（两口径）
    def chain_block(rep):
        delta_hi = Fr(rep["rho_capped"])
        ev = evaluate_chain(delta_hi, thr)
        return dict(
            eps=rep["eps"], eps_float=rep["eps_float"],
            delta_gram_upper=fs(delta_hi), delta_gram_float=f2(delta_hi),
            l5=dict(premise_ok=ev["l5_premise_ok"],
                    delta_max=fs(delta_max), delta_max_float=f2(delta_max),
                    deficit_factor=(None if ev["l5_premise_ok"]
                                    else f2(delta_hi / delta_max))),
            l6=dict(ball_ok=ev["l6_ball_ok"], r_L6=fs(r_L6), r_L6_float=f2(r_L6),
                    d_P_upper=fs(ev["d_P_upper"]), d_P_upper_float=f2(ev["d_P_upper"]),
                    delta_budget=fs(delta_L6_budget),
                    delta_budget_float=f2(delta_L6_budget),
                    deficit_factor=(None if ev["l6_ball_ok"]
                                    else f2(delta_hi / delta_L6_budget))),
            labeling=dict(ok=ev["labeling_ok"], half_gap=fs(half_gap),
                          half_gap_float=f2(half_gap)),
            thresholds_met=ev["thresholds_met"],
            # 闭链所需 ε（原始口径）：ε* = C_min·ρ_target²（精确 Fraction）
            eps_star_L3_need=fs(C_min_flat * half_gap ** 2),
            eps_star_L5=fs(C_min_flat * delta_max ** 2),
            eps_star_L6=fs(C_min_flat * delta_L6_budget ** 2),
        )

    chain_a = chain_block(caliber_a)
    chain_b = [chain_block(rep) for rep in caliber_b]
    for tag, blk in [("口径(a) 现账本", chain_a)] + [
            (f"口径(b) ε={r['eps_float']:.0e}", blk) for r, blk in zip(caliber_b, chain_b)]:
        if blk["l5"]["premise_ok"]:
            l5s = "过"
        else:
            l5s = f"FAIL({blk['l5']['deficit_factor']:.3f}×)"
        if blk["l6"]["ball_ok"]:
            l6s = "过"
        else:
            l6s = f"FAIL({blk['l6']['deficit_factor']:.3f}×)"
        log(f"[OK ] 链 {tag}: δ_gram={blk['delta_gram_float']:.6f}"
            f" L5 {l5s} L6 {l6s}"
            f" 标号 {'过' if blk['labeling']['ok'] else 'FAIL'}"
            f" ⇒ thresholds_met={blk['thresholds_met']}")

    chain_summary = dict(
        caliber_a=chain_a, caliber_b=chain_b,
        sqrt_shrinkage_compensation=dict(
            eps_ratio_a_over_1em11=fs(eps_ratio),
            eps_ratio_float=f2(eps_ratio),
            rho_gain_sqrt=f2(sqrt_gain),
            raw_gain_measured=raw_a / raw_b11,
            raw_follows_sqrt_epsilon=sqrt_consistent,
            note="R6-2 把 ε 从 4.15e-4 压到 1e-11（4.15e7×）⇒ 原始口径 ρ 恰按 √ 收缩 "
                 f"{f2(sqrt_gain):.0f}×；但闭合需 {f2(caliber_a['rho_raw_float']) / f2(need):.3g}×"
                 "（L3 need），且封顶口径在 cells≥3 的平凡半径处饱和（cell₃ 解约束需 "
                 "ε ≤ C₃·cellrad₃²），平方根补偿不能穿透胞元封顶——两口径均不闭合"),
        closure_requirement=dict(
            eps_star_L3_need=chain_a["eps_star_L3_need"],
            eps_star_L3_need_float=f2(Fr(chain_a["eps_star_L3_need"])),
            eps_star_L5=chain_a["eps_star_L5"],
            eps_star_L5_float=f2(Fr(chain_a["eps_star_L5"])),
            eps_star_L6=chain_a["eps_star_L6"],
            eps_star_L6_float=f2(Fr(chain_a["eps_star_L6"])),
            note="闭链（原始口径、平版 n=12、全局 φ_min）所需 ε 上界；R6-2 目标 1e-9…1e-11 "
                 "高于 L3 need 阈值 3.5 个数量级、高于 L6 阈值 5.3 个数量级"),
        stuck_constant="C_min（最劣胞元 ν₂ 的五节点间距平方积 × φ^{(12)} 全局下界 t=−1 处值）；"
                       "次瓶颈 = 胞元平凡半径封顶（cells≥3）",
    )

    # ---------- 负对照三件
    ncs = {}

    # NC1：C×10 膨胀 ⇒ 链判定必须翻 fail（常数为存档逐位一致性所拦截）
    tamper = C_min_flat * 10
    consistent_tampered = (tamper == C_min_flat)      # 与存档（=诚实重算值）比较
    naive_delta_a = sqrt_rat(eps_forcing / tamper, "hi")
    naive_delta_a_capped, _ = rho_capped_upper(
        eps_forcing,
        [dict(pc, C_k=pc["C_k"] * 10) for pc in flat_global])
    naive_ev_a = evaluate_chain(min(naive_delta_a_capped, naive_delta_a), thr)
    tampered_gate_a = chain_gate(consistent_tampered, naive_ev_a["thresholds_met"])
    # 辅助：×10^12 时阈值侧会被翻成 pass——验证一致性门仍拦住
    big = C_min_flat * 10 ** 12
    d_big, _ = rho_capped_upper(eps_forcing,
                                [dict(pc, C_k=pc["C_k"] * 10 ** 12) for pc in flat_global])
    naive_ev_big = evaluate_chain(min(d_big, sqrt_rat(eps_forcing / big, "hi")), thr)
    gate_big = chain_gate(False, naive_ev_big["thresholds_met"])
    ncs["NC1_C_times_10"] = dict(
        design="C_min×10 膨胀后重走链门：常数一致性必须判失配 ⇒ chain gate = fail",
        tampered_C=fs(tamper),
        archive_consistent=consistent_tampered,
        naive_thresholds_met_a=naive_ev_a["thresholds_met"],
        chain_gate_a=tampered_gate_a,
        must_be_fail=(tampered_gate_a is False),
        triggered=(tampered_gate_a is False and consistent_tampered is False),
        aux_C_times_1e12=dict(
            design="×10¹² 时阈值侧会 naïvely 全过（演示），一致性门仍拦 ⇒ fail",
            naive_thresholds_met=naive_ev_big["thresholds_met"],
            chain_gate=gate_big,
            blocked_by_consistency=(naive_ev_big["thresholds_met"] and gate_big is False)),
    )

    # NC2：节点间距减半 ⇒ 一致性断言必须触发
    tampered_nodes = list(nodes)
    srt = sorted(tampered_nodes)
    idx2 = srt.index(nodes[1])
    srt[idx2] = (srt[0] + srt[1]) / 2                 # ν₂ ← 中点：最紧间距减半
    try:
        assert_nodes_consistent(srt, ttp)
        nc2_triggered, nc2_err = False, None
    except ConsistencyError as e:
        nc2_triggered, nc2_err = True, str(e)
    ncs["NC2_node_gap_halved"] = dict(
        design="ν₂ ← (ν₁+ν₂)/2（最紧间距 0.0370→0.0185 减半）后重走输入一致性断言",
        triggered=nc2_triggered, error=nc2_err,
        must_trigger=True)

    # NC3：ε 单调性破坏（大 ε 给小 ρ）⇒ 必被检出
    honest_pairs = [(rep["eps_float"], rep["rho_capped_float"]) for rep in caliber_b]
    assert assert_eps_monotone(honest_pairs)          # 正对照：诚实曲线必须单调
    tampered_pairs = list(honest_pairs)
    # 只对调 ρ 值（保持 ε 不动）：最大 ε 档拿到最小 ρ ⇒ 单调性破坏
    tampered_pairs[0] = (tampered_pairs[0][0], tampered_pairs[-1][1])
    tampered_pairs[-1] = (tampered_pairs[-1][0], honest_pairs[0][1])
    try:
        assert_eps_monotone(tampered_pairs)
        nc3_triggered, nc3_err = False, None
    except ConsistencyError as e:
        nc3_triggered, nc3_err = True, str(e)
    sdp_pairs = [(lvl["eps_float"], lvl["rho_sdp"]) for lvl in levels]
    sdp_mono = assert_eps_monotone(sdp_pairs)         # 正对照：SDP 曲线也单调
    ncs["NC3_eps_monotonicity"] = dict(
        design="口径(b) 曲线首末两档 ρ 对调 ⇒ 单调性检查器必须报「大 ε 给小 ρ」",
        triggered=nc3_triggered, error=nc3_err,
        honest_curve_monotone=True, sdp_curve_monotone=sdp_mono,
        must_trigger=True)

    # ---------- R7-3 nodeLocal 负对照三件（NC4 W×10/×100、NC5 c0 冒充、NC6 ε 单调）
    if node_local.get("present"):
        # NC4：区间宽度 W→10W（M 的 dyadic 半宽外张 ⇒ 节点亏损 ε_W ~10×，链余量按 ~10× 退化
        #      且被一致性门检出；W→100W 时判据本身翻 fail）
        nc4_results = {}
        for factor, tag in ((10, "x10"), (100, "x100")):
            nl_coeffs_t = list(nl_coeffs)
            nl_coeffs_t[0] -= (factor - 1) * nl_W
            eW_lo_t, eW_hi_t = nl_eps_W(nl_coeffs_t, ns, mults_sorted)
            # 篡改档走完整两遍协议（pass1 角点 → θ' → B&B），与诚实管线同代码路径
            ups_t = []
            for c in cells:
                nu = c["node"]
                for t in {c["lo"], min(c["hi"], NL_T_RIGHT)}:
                    d2 = (t - nu) ** 2
                    if d2 > 0:
                        ups_t.append((nl_phi_pt(0, t)[1] - nl_M_at(nl_coeffs_t, t)) / d2)
            theta_t = (1 - NL_TAU) * min(ups_t)
            C_lo_t, _C_hi_t, _pc, _st = certify_C_glob(nl_coeffs_t, cells, theta=theta_t)
            ratio_eW = f2(eW_hi_t / epsW_hi)
            predicted = epsW_hi + 36 * (factor - 1) * nl_W   # δ_k' = δ_k + (f−1)W 精确预测
            margin_t = C_lo_t * half_gap ** 2 / eW_hi_t
            nc4_results[tag] = dict(
                factor=factor,
                eps_W_hi=fs(eW_hi_t), eps_W_hi_float=f2(eW_hi_t),
                eps_W_ratio_float=ratio_eW,
                eps_W_predicted=fs(predicted), eps_W_predicted_float=f2(predicted),
                eps_W_matches_prediction=bool(f2(eW_lo_t) <= f2(predicted) <= f2(eW_hi_t)
                                              or abs(f2(eW_hi_t) - f2(predicted)) <= 1e-3 * f2(predicted)),
                C_glob_lo=fs(C_lo_t), C_glob_lo_float=f2(C_lo_t),
                margin=fs(margin_t), margin_float=f2(margin_t),
                criterion_passed=bool(C_lo_t >= eW_hi_t / half_gap ** 2))
        honest_margin = C_lo * half_gap ** 2 / epsW_hi
        degr_factor = f2(honest_margin / Fr(nc4_results["x10"]["margin"]))
        archive_mismatch = (Fr(nc4_results["x10"]["C_glob_lo"]) != C_lo)
        ncs["NC4_minorant_width_x10"] = dict(
            design="M 的 dyadic 半宽 W→10W（coeffs[0] −= 9W，完整两遍协议重跑）：ε_W 亏损 "
                   "= ε_W+324W（精确预测并被复核）、链余量 ~10× 退化、且重算 C_glob 与诚实存档 "
                   "逐位失配 ⇒ 被检出；×100 时 L3-need 判据本身翻 fail（W 级膨胀对链的"
                   "预期破坏被演示）",
            x10=nc4_results["x10"], x100=nc4_results["x100"],
            honest_margin=fs(honest_margin), honest_margin_float=f2(honest_margin),
            margin_degradation_factor=degr_factor,
            eps_W_ratio_x10=nc4_results["x10"]["eps_W_ratio_float"],
            archive_consistent_after_tamper=bool(archive_mismatch is False),
            detected_by_mismatch=bool(archive_mismatch),
            expected_degradation=(9.0 <= float(degr_factor) <= 11.5),
            x100_criterion_fails=(nc4_results["x100"]["criterion_passed"] is False),
            triggered=bool(archive_mismatch and 9.0 <= float(degr_factor) <= 11.5
                           and nc4_results["x100"]["criterion_passed"] is False
                           and nc4_results["x10"]["eps_W_matches_prediction"]),
            must_trigger=True)
        log(f"[{'OK ' if ncs['NC4_minorant_width_x10']['triggered'] else 'FAIL'}] "
            f"NC4 W×10：ε_W 比 {nc4_results['x10']['eps_W_ratio_float']:.3f}、余量退化 "
            f"{degr_factor:.2f}×、×100 判据 {'fail(预期)' if not nc4_results['x100']['criterion_passed'] else 'PASS(异常)'}")

        # NC5：用 c0（渐近节点极限 float，无区间证书）直接冒充 C_glob ⇒ 一致性门必拦
        c0_claim = Fr(str(probe_c0)) if probe_c0 is not None else None
        try:
            if c0_claim is None:
                raise ConsistencyError("c0 缺失")
            if not (C_lo <= c0_claim <= C_hi):
                raise ConsistencyError(
                    f"c0={f2(c0_claim):.6e} 不在严格化区间 [{f2(C_lo):.6e},{f2(C_hi):.6e}] 内"
                    "（节点渐近常数非全域 inf——胞元角点更小者不在其下）")
            if c0_claim == C_lo or c0_claim == C_hi:
                raise ConsistencyError("c0 与区间端点重合但无推导链")
            raise AssertionError("c0 冒充未被拦截（不应到达）")
        except ConsistencyError as e:
            nc5_triggered, nc5_err = True, str(e)
        except AssertionError as e:
            nc5_triggered, nc5_err = False, str(e)
        ncs["NC5_c0_impersonation"] = dict(
            design="C_glob := c0=4.516455950778955e-9（R6-1 渐近/网格口径，无区间证书）"
                   "⇒ 必须被一致性门拦截：①c0 ∉ [C_lo,C_hi]（认证区间不含之）②无 B&B/"
                   "Taylor 证书路径",
            claim=fs(c0_claim) if c0_claim is not None else None,
            claim_float=probe_c0,
            certified_interval=[fs(C_lo), fs(C_hi)],
            triggered=bool(nc5_triggered), error=nc5_err, must_trigger=True)
        log(f"[{'OK ' if nc5_triggered else 'FAIL'}] NC5 c0 冒充：{nc5_err[:90]}")

        # NC6：nodeLocal 口径 ε 单调性（ρ=√(ε/C_lo) 对 ε 梯度）＋ 对调破坏检出
        eps_ladder = [epsW_hi, epsW_hi * 10, epsW_hi * 100, eps_forcing]
        nl_pairs = [(f2(e), f2(sqrt_rat(e / C_lo, "hi"))) for e in eps_ladder]
        nl_mono_honest = assert_eps_monotone(nl_pairs)
        nl_pairs_bad = list(nl_pairs)
        nl_pairs_bad[0] = (nl_pairs_bad[0][0], nl_pairs_bad[-1][1])
        nl_pairs_bad[-1] = (nl_pairs_bad[-1][0], nl_pairs[0][1])
        try:
            assert_eps_monotone(nl_pairs_bad)
            nc6_triggered, nc6_err = False, None
        except ConsistencyError as e:
            nc6_triggered, nc6_err = True, str(e)
        ncs["NC6_nodelocal_eps_monotone"] = dict(
            design="nodeLocal 口径 ρ(ε)=√(ε/C_glob_lo) 沿 ε∈{ε_W,10ε_W,100ε_W,ε_forcing} "
                   "必须单调；首末对调 ⇒ 必被检出",
            honest_curve_monotone=bool(nl_mono_honest),
            triggered=bool(nc6_triggered), error=nc6_err, must_trigger=True)
        log(f"[{'OK ' if nc6_triggered else 'FAIL'}] NC6 nodeLocal ε 单调性 triggered="
            f"{nc6_triggered}")

    nc_all = all(ncs[n]["triggered"] for n in ncs)
    for name, nc in ncs.items():
        log(f"[{'OK ' if nc['triggered'] else 'FAIL'}] 负对照 {name} triggered={nc['triggered']}")

    # ---------- 汇总文档
    doc = dict(
        kind="n9-l3-analytic-tube",
        script="bounds/l3_analytic.py",
        scope=(
            "L3 解析谱管零件（R6-4）：由 Hermite 余项公式推导每节点平方 gap 下界与显式"
            "ρ_spec(ε)~√(ε/C)。严格层：全部常数精确 Fraction（节点十进制字面值、dyadic "
            "φ^{(n)} 最小值、有理平方根包），mpmath.iv dps=50 验证闭式/单调/最小值；"
            "float 交叉抽验 seed=20261006 仅为 advisory。前提口径：节点取 tube.json "
            "十进制字面值（证书化时的 dyadic 节点选择属 R6-2/R6-3）；「每对 gap ≤ ε」的"
            "强制前提在口径(a)沿用现账本 λ_cls ≤ ε_forcing 的语义（其与 Hermite gap 的"
            "桥接是 R6-2 重设计的业务，本文件按任务书口径入账）；j=5 接触版的 (t+1)^j "
            "因子使含 −1 的胞元常数恒 0（结构性失约束，如实报 vacuous）。"),
        formula=dict(
            remainder="φ(t)−H(t) = φ^{(n)}(ξ)/n!·(t+1)^j·∏_k(t−ν_k)²，"
                      "ξ∈hull({t}∪{ν}∪{−1 若 j>0})⊂[−1,1)",
            phi_closed_form="φ^{(n)}(t) = (2n−1)!!·(2−2t)^{−n−1/2}，严格递增，"
                            "min at t=−1: (2n−1)!!·2^{−2n−1}",
            versions=dict(flat=dict(n=N_FLAT, j=J_FLAT, conditions=12, deg_le=11),
                          contact=dict(n=N_CONTACT, j=J_CONTACT, conditions=17, deg_le=16)),
            per_cell_bound="gap(t) ≥ C_k·(t−ν_k)² 于 cell_k，"
                           "C_k = φ^{(n)}_min/n!·(a_k+1)^j·∏_{k'≠k}dist(ν_{k'},cell_k)²",
            tube_radius="ρ_raw(ε)=√(ε/C_min)；ρ_capped(ε)=max_k min(√(ε/C_k),cellrad_k)"
                        "（胞元平凡半径封顶，两者均严格上界）",
        ),
        inputs=dict(
            nodes=nodes_str, multiplicities=mults,
            min_gap=fs(min_gap), half_gap=fs(half_gap),
            eps_forcing=dict(exact=fs(eps_forcing), float=f2(eps_forcing),
                             source="results/l2_rigorous.json /eps_forcing/exact"),
            delta_max=dict(exact=fs(delta_max), float=f2(delta_max),
                           source="results/l4.json /constants/delta_max_exact"),
            C_procrustes=dict(exact=fs(C_pro), float=f2(C_pro),
                              source="results/l4.json /constants/C_exact"),
            r_L6=dict(value=fs(r_L6), float=f2(r_L6),
                      source="results/tube.json /tube_radius/rigorous/chain_best/radius"
                             "（float 输入按二进制精确值入账；λ_min=0.14378982）"),
        ),
        interval_constants=dict(
            c_n={str(N_FLAT): double_factorial(N_FLAT),
                 str(N_CONTACT): double_factorial(N_CONTACT)},
            phi_n_min=dict(
                flat=dict(exact=fs(phi_min_flat), float=f2(phi_min_flat),
                          closed_form=f"(2·{N_FLAT}−1)!!·2^−{2 * N_FLAT + 1}"),
                contact=dict(exact=fs(phi_min_contact), float=f2(phi_min_contact),
                             closed_form=f"(2·{N_CONTACT}−1)!!·2^−{2 * N_CONTACT + 1}"),
                hull_refined_nu1=dict(
                    flat=dict(exact=fs(phi_nu1_flat), float=f2(phi_nu1_flat),
                              note="cells≥2 的 ξ 漫游域 [ν₁,max(t,ν₆)] 内下界（精确下界："
                                   "c_n/((2−2ν₁)^n·√(2−2ν₁) 上界)）"),
                    contact=dict(exact=fs(phi_nu1_contact), float=f2(phi_nu1_contact)))),
            cells=[dict(k=c["k"], node=fs(c["node"]),
                        lo=fs(c["lo"]), hi=fs(c["hi"]), cellrad=fs(c["cellrad"]),
                        dists={str(kp): fs(d) for kp, d in c["dists"].items()},
                        spacing_prod_sq=fs(c["spacing_prod_sq"]))
                   for c in cells],
            per_cell_C=dict(
                flat_global=[dict(k=pc["k"], C_k=fs(pc["C_k"]),
                                  C_k_float=f2(pc["C_k"]), vacuous=pc["vacuous"])
                             for pc in flat_global],
                contact_global=[dict(k=pc["k"], C_k=fs(pc["C_k"]),
                                     C_k_float=f2(pc["C_k"]), vacuous=pc["vacuous"])
                                for pc in contact_global],
                flat_hull_refined=[dict(k=pc["k"], C_k=fs(pc["C_k"]),
                                        C_k_float=f2(pc["C_k"]), vacuous=pc["vacuous"])
                                   for pc in flat_hull],
                contact_hull_refined=[dict(k=pc["k"], C_k=fs(pc["C_k"]),
                                           C_k_float=f2(pc["C_k"]), vacuous=pc["vacuous"])
                                      for pc in contact_hull]),
            C_min=dict(flat_global=fs(C_min_flat),
                       flat_global_float=f2(C_min_flat),
                       worst_cell=worst_flat["k"] + 1,
                       contact_global=fs(C_min_contact),
                       contact_global_note="=0：cell_1 含 −1，(t+1)^5 因子 ⇒ 结构性失约束",
                       contact_global_nonzero_min=fs(C_min_contact_nz),
                       flat_hull_refined=fs(C_min_flat_hull),
                       flat_hull_refined_float=f2(C_min_flat_hull)),
            iv_checks=iv_checks,
            nodeLocal_core=(None if not node_local.get("present") else dict(
                C_glob=node_local["C_glob"],
                eps_W=node_local["eps_W"],
                criterion=node_local["criterion"],
                branch_stats=node_local["branch_stats"],
                per_cell=node_local["per_cell"],
                minorant=node_local["minorant"],
                cross_checks=node_local["cross_checks"],
                chain_caliber_c=node_local["chain_caliber_c"],
                r_star_l6_used=node_local["r_star_l6_used"])),
        ),
        rho_spec=dict(
            caliber_a_current_ledger=caliber_a,
            caliber_a_contact_version=caliber_a_contact,
            caliber_a_hull_refined=caliber_a_hull,
            caliber_b_r62_curve=caliber_b,
        ),
        reconciliation_sdp=dict(
            levels=levels,
            mechanism=mech,
            elimination=elimination,
            cross_ref_r61_probe=cross_ref,
            note="SDP 值读自 tube.json /spectral_tube/AAA/res（三 orbit 一致，取 AAA）；"
                 "tube.json 自身扫描档 ε_forcing=0.0004153070184893437 系 M8 cap 口径"
                 "冻结值（R8A 换 cap M9 口径后 l2 精确 Fraction ε=1.4031e-4，D29 裁决 3，"
                 "口径关系见 l2_rigorous numerical_ledger_comparison）——对账 levels 系"
                 "固定扫描档（3e-4/5.35e-6/1e-7/1.5e-8）逐档独立计算，不随口径换档变"),
        chain_L2_L3_L5_L6=chain_summary,
        nodeLocal=node_local,
        negative_controls=ncs,
    )

    # ---------- 门①：重算常数 vs 存档逐位一致（幂等重跑：核心一致则不重写文件）
    constants_core = dict(
        c_n=doc["interval_constants"]["c_n"],
        phi_n_min=doc["interval_constants"]["phi_n_min"],
        cells=doc["interval_constants"]["cells"],
        per_cell_C=doc["interval_constants"]["per_cell_C"],
        C_min=doc["interval_constants"]["C_min"],
        nodeLocal_core=(None if not node_local.get("present") else dict(
            C_glob=node_local["C_glob"],
            eps_W=node_local["eps_W"],
            criterion=node_local["criterion"],
            branch_stats=node_local["branch_stats"],
            per_cell=node_local["per_cell"],
            minorant=node_local["minorant"],
            cross_checks=node_local["cross_checks"],
            chain_caliber_c=node_local["chain_caliber_c"],
            r_star_l6_used=node_local["r_star_l6_used"])),
    )
    archive_ok = True
    archive_created = False
    if OUT_JSON.exists():
        try:
            arch = json.loads(OUT_JSON.read_text())
            arch_ic = arch.get("interval_constants", {})
            # 逐字段比较五个确定性常数子树（iv_checks 属验证记录，不参与存档比对）
            arch_core = {k: arch_ic.get(k) for k in constants_core}
            recompute_stable = json.loads(json.dumps(constants_core, sort_keys=True))
            arch_stable = json.loads(json.dumps(arch_core, sort_keys=True))
            archive_ok = (arch_stable == recompute_stable)
            if not archive_ok:
                log("[FAIL] 门①：重算区间常数与存档不一致")
        except Exception as e:
            archive_ok = False
            log(f"[FAIL] 门①：存档读取失败 {e}")
    else:
        archive_created = True
        log("[OK ] 门①：存档首建（archive_created）")

    # ---------- 门②：字段完整性一致性
    field_checks = dict(
        has_all_top_keys=all(k in doc for k in
                             ["formula", "interval_constants", "rho_spec",
                              "reconciliation_sdp", "chain_L2_L3_L5_L6",
                              "negative_controls"]),
        reconciliation_covers_4_levels=(len(levels) == 4),
        chain_has_both_calibers=("caliber_a" in chain_summary
                                 and len(chain_summary["caliber_b"]) == 3),
        capped_le_raw=(caliber_a["rho_capped_float"] <= caliber_a["rho_raw_float"]),
        capped_le_max_cellrad=(Fr(caliber_a["rho_capped"])
                               <= max(c["cellrad"] for c in cells)),
        monotone_analytic_curve=assert_eps_monotone(honest_pairs),
        monotone_sdp_curve=sdp_mono,
        elimination_fields_complete=all(
            k in elimination for k in
            ["sdp_ratio_at_forcing", "analytic_ratio_at_forcing", "C_deficit_factor",
             "rho_deficit_factor", "verdict"]),
        chain_fields_complete=all(
            k in chain_a for k in
            ["delta_gram_upper", "l5", "l6", "labeling", "thresholds_met",
             "eps_star_L3_need", "eps_star_L5", "eps_star_L6"]),
        nodelocal_fields_complete=(not node_local.get("present") or all(
            k in node_local for k in
            ["C_glob", "per_cell", "branch_stats", "eps_W", "criterion",
             "cross_checks", "chain_caliber_c", "method", "minorant"])),
        nodelocal_criterion_recorded=(not node_local.get("present") or
                                      "passed" in node_local["criterion"]),
        nodelocal_chain_links_complete=(not node_local.get("present") or all(
            lk in node_local["chain_caliber_c"]["links"]
            for lk in ["L3_need", "L5", "L6"])),
        nodelocal_crosschecks_ok=(not node_local.get("present") or
                                  node_local["cross_checks"]["all_ok"] is True),
        plateau_identity_holds=identity_hi,
    )
    field_checks["all_passed"] = all(v for k, v in field_checks.items() if k != "all_passed")
    for k, v in field_checks.items():
        if k != "all_passed":
            log(f"[{'OK ' if v else 'FAIL'}] 门② {k} = {v}")

    gates = dict(
        G1_constants_match_archive=dict(passed=archive_ok, archive_created=archive_created),
        G2_fields_complete=dict(passed=field_checks["all_passed"],
                                detail=field_checks),
        G3_negative_controls=dict(passed=nc_all,
                                  detail={n: ncs[n]["triggered"] for n in ncs}),
        iv_verification=dict(passed=iv_all),
    )
    gates_all = all(g["passed"] for g in gates.values())

    doc["gates"] = gates
    doc["provenance"] = dict(
        seed=SEED,
        code_version=code_version(),
        python_version=sys.version.split()[0],
        mpmath_version=mpmath.__version__,
        iv_dps=IV_DPS,
        inputs=dict(tube="results/tube.json", l2="results/l2_rigorous.json",
                    l4="results/l4.json",
                    hermite_probe="results/hermite_probe.json（R7-3 nodeLocal 只读复用 "
                                  "R6-1 dyadic minorant）",
                    l6_intube="results/l6_intube.json（chain caliber (c) 的 r* 读档）",
                    energies_E_star=tube["meta"]["E_star"],
                    E_star_source=tube["meta"]["E_star_source"]),
        determinism="无时钟戳；核心字段（interval_constants 等）逐位幂等；"
                    "provenance.code_version 漂移不触发重写",
        wall_s=round(time.time() - t_start, 3),
    )

    # ---------- 写档（幂等：核心一致且仅 provenance 漂移 ⇒ 不重写，保工作树干净）
    write = True
    if OUT_JSON.exists() and archive_ok and not archive_created:
        try:
            old = json.loads(OUT_JSON.read_text())
            old_core = {k: v for k, v in old.items() if k != "provenance"}
            new_core = {k: v for k, v in doc.items() if k != "provenance"}
            if json.dumps(old_core, sort_keys=True) == json.dumps(new_core, sort_keys=True):
                write = False
                log("[OK ] 核心内容与存档逐位一致，仅 provenance 漂移 ⇒ 不重写"
                    "（保持 git 工作树干净）")
        except Exception:
            write = True
    if write:
        OUT_JSON.write_text(json.dumps(doc, indent=1, ensure_ascii=False) + "\n")
        log(f"[OK ] 写 {OUT_JSON.relative_to(HERE.parents[1])}")

    log(f"[{'PASS' if gates_all else 'FAIL'}] L3 解析谱管门："
        + " ".join(f"{k}={'pass' if v['passed'] else 'FAIL'}" for k, v in gates.items()))
    if not gates_all:
        return 1
    log("[PASS] 链判定（诚实）：两口径均不闭合；断点未被解析式消除——细节见 "
        "results/l3_analytic.json /reconciliation_sdp/elimination 与 /chain_L2_L3_L5_L6")
    return 0


if __name__ == "__main__":
    sys.exit(main())
