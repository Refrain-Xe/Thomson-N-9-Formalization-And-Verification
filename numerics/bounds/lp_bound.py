#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Thomson N=9 的 Yudin 型两点 LP 严格下界（插值多项式 minorant 的对偶形式）。

方法（Delsarte–Yudin 两点线性规划界，对偶 = 多项式 minorant）：
    对球面 S^2 上 N=9 点，库仑对势 phi(t) = (2-2t)^{-1/2}（t = x·y）。
    取多项式 f(t) = Σ_{k=0}^{d} c_k P_k(t)（Legendre 基）满足
        (i)  c_k >= 0  对一切 k >= 1（P_k 在 S^2 上正定，加法定理）；
        (ii) f(t) <= phi(t) 对一切 t ∈ [-1, 1)。
    则对任意 9 点构型（利用 Σ_{i,j} P_k(x_i·x_j) = (4π/(2k+1)) Σ_m |Σ_i Y_km(x_i)|^2 >= 0）：
        E = Σ_{i<j} phi(x_i·x_j) >= Σ_{i<j} f(x_i·x_j)
          = ½(Σ_{i,j} f(x_i·x_j) − N f(1)) >= (N² c_0 − N f(1)) / 2。
    LP（在稠密格点上离散 (ii)）最大化该下界；LP 解只是【候选】，随后：
      1) 系数向下舍入到分母 2^64 的有理数（k>=1 的系数保持 >= 0）；
      2) 用【纯精确有理算术】认证 (i)(ii)：
         - (i) 由构造精确成立（Fraction 比较）；
         - (ii) 用二分分支定界扫过 [-1,1)：每叶以中点 Taylor 展开
           sup f <= Σ_{k<=K} |f^{(k)}(m)/k!| h^k + h^{K+1}·S_tail（全精确有理数，
           截断尾项用 |f^{(k)}(m)/k!| <= Σ_j |p_j| C(j,k) 严格控制），
           inf phi >= max( phi(a) 的精确下界, phi(m) − h·phi'(b) 的精确上界 )，
           其中 1/√x 的下/上界由整数平方根 math.isqrt 精确给出（无浮点、无区间库）；
         - 扫描给出 sup(f−phi) <= M 的严格上界，取 η = M + 2^-46 平移 c_0，
           得到 f̂ = f − η 满足 f̂ <= phi 于 [-1,1)（严格证书）；
      3) 下界 B = (N² ĉ_0 − N f̂(1))/2 用 Fraction 精确计算，报告值向下取 9 位小数。
    证书不信任 LP 求解器的任何浮点结果：LP 只负责"找"候选多项式。

输出：bounds/results/lp.json（bound、精确值、方法参数、证书、时间戳）。
      违反 0 < bound <= E* + 1e-6 时打印原因并以 sys.exit(1) 退出。

用法：python3 lp_bound.py [--deg 40] [--ngrid 60000] [--no-selftest] [--out PATH]
依赖：numpy, scipy（本机已装）。确定性流水线；随机种子固定（防御性）。
"""
import argparse
import json
import math
import subprocess
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

import numpy as np
from numpy.polynomial import legendre as L
from scipy.optimize import linprog

# ------------------------------------------------------------------ 配置
CFG = dict(
    N=9,
    DEG=40,            # 多项式次数
    NGRID=60000,       # LP 约束格点数（[-1, 1-1e-9] 均匀）
    SEED=20261002,     # 固定随机种子（流水线本身确定性，种子防御性固定）
    ROUND_BITS=64,     # LP 系数向下舍入到 2^-64 网格
    LP_TOL=1e-10,      # HiGHS primal feasibility tolerance（合法下限 1e-10）
    FIRST_LEVEL=2048,  # 扫描第一层等分区间数（[-1, TOP]）
    TAIL_EXP=40,       # TOP = 1 - 2^-40，其上由尾部引理覆盖
    W_MIN_EXP=22,      # 分支定界最小叶宽 2^-22
    TAYLOR_K=6,        # Taylor 精确项数（k=0..K），尾部严格控制
    PHI_P=60,          # phi 有理界的分辨率 2^-60
    ETA_MARGIN=Fraction(1, 2**46),  # 平移 η 的安全余量
    REPORT_DEC=9,      # 报告值保留小数位（向下取整）
    SELFTEST=(2, 3, 4, 6, 12),  # 已知精确最优能的 LP 校准 N
)

F0, F1 = Fraction(0), Fraction(1)


def code_version() -> str:
    """产物 provenance 的代码版本（git describe --always --dirty；沿 sdp_certify.py 惯例）。"""
    try:
        return subprocess.check_output(
            ["git", "describe", "--always", "--dirty"],
            cwd=str(Path(__file__).resolve().parents[1]),
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown(non-git)"

# ----------------------------------------------------- 精确多项式工具（Fraction）
def pmul(A, B):
    R = [F0] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        if a:
            for j, b in enumerate(B):
                R[i + j] += a * b
    return R

def padd(A, B):
    n = max(len(A), len(B))
    R = [F0] * n
    for i, a in enumerate(A):
        R[i] += a
    for i, b in enumerate(B):
        R[i] += b
    return R

def pscale(A, s):
    return [a * s for a in A]

def horner(A, t):
    r = F0
    for a in reversed(A):
        r = r * t + a
    return r

def legendre_power_basis(d):
    """P_0..P_d 的幂基系数表（升幂），全精确。递推：
    P_0 = 1, P_1 = x, (k+1)P_{k+1} = (2k+1)xP_k − kP_{k−1}（k>=1）。"""
    LEG = [[F1], [F0, F1]]
    Pk, Pkm1 = [F0, F1], [F1]
    for k in range(1, d):                      # 生成 P_{k+1} = P_2..P_d
        Pn = pscale(pmul([F0, F1], Pk), 2 * k + 1)
        Pn = padd(Pn, pscale(Pkm1, -k))
        Pn = pscale(Pn, Fraction(1, k + 1))
        LEG.append(Pn)
        Pkm1, Pk = Pk, Pn
    assert len(LEG) == d + 1
    return LEG

# ----------------------------------------------------- phi 的精确有理界（isqrt）
def sqrt_inv_bounds(s: Fraction, p: int):
    """s > 0 有理数。返回 (lo, hi) 满足 lo <= 1/sqrt(s) <= hi，精确有理数。"""
    assert s > 0
    # 1/sqrt(s) = sqrt(s_den/s_num) = sqrt(s_den*s_num)/s_num
    q = math.isqrt((4 ** p) * s.denominator * s.numerator) // s.numerator
    lo = Fraction(q, 2 ** p)                   # floor => lo <= 1/sqrt(s)
    hi = Fraction(q + 1, 2 ** p)               # ceil  => hi >= 1/sqrt(s)
    return lo, hi

def phi_lower(a: Fraction, p: int):
    """精确下界：<= phi(a) = (2-2a)^{-1/2}（要求 a < 1）。"""
    return sqrt_inv_bounds(2 - 2 * a, p)[0]

def phi_prime_upper(b: Fraction, p: int):
    """精确上界：>= phi'(b) = (2-2b)^{-3/2}（要求 b < 1）。"""
    phi_hi = sqrt_inv_bounds(2 - 2 * b, p)[1]
    return phi_hi / (2 - 2 * b)

# ----------------------------------------------------- LP（数值，仅产生候选）
def phi_np(t):
    return 1.0 / np.sqrt(2.0 - 2.0 * t)

def solve_lp(N, deg, ngrid, tol, seed):
    """Yudin LP：max (N²c0 − N f(1))/2, s.t. f<=phi 于格点, c_k>=0 (k>=1)。
    返回 (lp_value, coeffs)。"""
    rng = np.random.default_rng(seed)          # 种子固定；本函数未用随机性
    del rng
    tgrid = np.linspace(-1.0, 1.0 - 1e-9, ngrid)
    c = np.zeros(deg + 1)
    c[0] = -(N * N - N) / 2.0                  # linprog 做最小化 => 取负
    c[1:] = N / 2.0
    res = linprog(
        c, A_ub=L.legvander(tgrid, deg), b_ub=phi_np(tgrid),
        bounds=[(None, None)] + [(0, None)] * deg,
        method="highs",
        options={"primal_feasibility_tolerance": tol},
    )
    if res.status != 0:
        raise RuntimeError(f"LP 求解失败: {res.message}")
    return -res.fun, res.x

# ----------------------------------------------------- 认证（纯精确算术）
def dyadic_floor(x: float, bits: int) -> Fraction:
    fx = Fraction(float(x))
    q = 2 ** bits
    v = Fraction((fx.numerator * q) // fx.denominator, q)   # 向下取整
    return v if v >= 0 else F0                              # 负值（容差）钳为 0

def taylor_tables(power):
    """TP[k][j] = f^{(k)}/k! 的幂基系数 = p_{j+k}·C(j+k,k)；及 T_k = Σ_j|p_j|C(j,k)。"""
    d = len(power) - 1
    TP = []
    for k in range(0, d + 1):
        row = [F0] * (d + 1 - k)
        for j in range(0, d + 1 - k):
            if j + k <= d:
                row[j] = power[j + k] * Fraction(math.comb(j + k, k))
        TP.append(row)
    T = []
    for k in range(0, d + 1):
        T.append(sum(abs(power[j]) * math.comb(j, k) for j in range(k, d + 1)))
    return TP, T

def certify(fr, power, cfg):
    """分支定界认证 f <= phi 于 [-1, TOP]，TOP = 1 - 2^-TAIL_EXP。

    每叶对 g = f − phi 用中点 Taylor（精确有理）：
        sup_{[a,b]} g <= Σ_{k<=K} |A_k| h^k + h^{K+1}·S_tail，
        A_k = g^{(k)}(m)/k! 的精确有理区间（f 部分精确，φ 部分由 isqrt 界），
        S_tail 用 |f^{(k)}(m)/k!| <= Σ_j |p_j| C(j,k) 与
        φ^{(k)}/k! = [C(2k,k)/4^k](2−2t)^{−1/2−k}（系数 <= 1）严格控制。
    叶内若 h/(2−2b) > 1/2（φ 幂级数尾项失控，仅发生在顶部，该处边距巨大），
    退回对 f、φ 分别界的形式。返回 sup(f−phi) 的严格上界 M 等。
    """
    d = len(power) - 1
    K = cfg["TAYLOR_K"]
    TP, T = taylor_tables(power)
    CC = [Fraction(math.comb(2 * k, k), 4 ** k) for k in range(0, d + 1)]  # φ^{(k)}/k! 系数
    TOP = 1 - Fraction(1, 2 ** cfg["TAIL_EXP"])
    span = TOP + 1
    W_MIN = Fraction(1, 2 ** cfg["W_MIN_EXP"])
    n0 = cfg["FIRST_LEVEL"]
    H_MAX = span / (2 * n0)                   # 所有叶的半宽上界
    S_tail_f = F0                             # f 尾：Σ_{k>K} |f^{(k)}(m)/k!| h^k <= h^{K+1}·S_tail_f
    for k in range(K + 1, d + 1):
        S_tail_f += T[k] * H_MAX ** (k - K - 1)

    def taylor_f_sup(a, b):
        """f 的 Taylor 上界（含严格尾项），对 |m|<=1, h<=H_MAX 有效。"""
        m, h = (a + b) / 2, (b - a) / 2
        s = abs(horner(TP[0], m))
        hk = F1
        for k in range(1, K + 1):
            hk *= h
            s += abs(horner(TP[k], m)) * hk
        return s + hk * h * S_tail_f

    def phi_inf_fallback(a, b):
        """分别界形式的 inf phi 下界。"""
        m, h = (a + b) / 2, (b - a) / 2
        cand = [phi_lower(a, cfg["PHI_P"])]
        if b < 1 - Fraction(1, 2 ** 20):
            cand.append(phi_lower(m, cfg["PHI_P"]) - h * phi_prime_upper(b, cfg["PHI_P"]))
        return max(cand)

    def leaf_bound(a, b):
        m, h = (a + b) / 2, (b - a) / 2
        inv = 2 - 2 * b                        # 叶内 2−2t >= 2−2b
        if h * 2 <= inv:                       # r = h/inv <= 1/2：g-形式可用
            lo1, hi1 = sqrt_inv_bounds(2 - 2 * m, cfg["PHI_P"])
            # k=0 项【保留符号】：sup g <= g(m) + Σ_{k>=1}|A_k| h^k（g(m) 的负值正是边距）
            s = horner(TP[0], m) - lo1         # <= f(m) − phi(m) <= g 的中点值上界
            hk = F1
            for k in range(1, K + 1):
                hk *= h
                fk = horner(TP[k], m)          # f^{(k)}(m)/k!，精确
                pk = CC[k] * (2 - 2 * m) ** (-k)   # 精确正有理因子
                ak_lo, ak_hi = fk - pk * hi1, fk - pk * lo1
                s += max(abs(ak_lo), abs(ak_hi)) * hk
            r = h / inv
            phi_tail = sqrt_inv_bounds(inv, cfg["PHI_P"])[1] * (r ** (K + 1)) / (1 - r)
            return s + hk * h * (S_tail_f + phi_tail)
        return taylor_f_sup(a, b) - phi_inf_fallback(a, b)

    t0 = time.time()
    stack = []
    for i in range(n0):
        stack.append((-1 + span * Fraction(i, n0), -1 + span * Fraction(i + 1, n0)))
    n_eval = n_pass = n_leaf = 0
    M = F0
    worst = None
    next_report = 30.0
    while stack:
        a, b = stack.pop()
        n_eval += 1
        bd = leaf_bound(a, b)
        if bd <= 0:
            n_pass += 1
        elif (b - a) <= W_MIN:
            n_leaf += 1
        else:
            mm = (a + b) / 2
            stack.append((a, mm))
            stack.append((mm, b))
            if time.time() - t0 > next_report:
                print(f"[cert] … {n_eval} 叶，栈 {len(stack)}，pass {n_pass}", flush=True)
                next_report += 30.0
            continue
        if bd > M:
            M, worst = bd, (a, b)
        if n_eval > 1_000_000:
            print("[cert] 熔断：叶评估超过 1e6，参数不当", flush=True)
            sys.exit(3)
    # 尾部 [TOP, 1)：f 的 Taylor 上界 vs phi(TOP) 的精确下界
    tb = taylor_f_sup(TOP, 1) - phi_lower(TOP, cfg["PHI_P"])
    tail_ok = tb <= 0
    if tb > M:
        M, worst = tb, (TOP, F1)
    return dict(M=M, worst=worst, n_eval=n_eval, n_pass=n_pass, n_leaf=n_leaf,
                tail_ok=tail_ok, tail_bound=tb, sweep_time=time.time() - t0)

# ----------------------------------------------------- 已知最优能（自检）
def exact_E(N):
    """返回 (E 值 float, 描述)。N∈{2,3,4,6} 精确闭式；12 用精确几何构造（icosahedron）。"""
    import mpmath as mp
    mp.mp.dps = 30
    if N == 2:
        return 0.5, "对径点对：1/2"
    if N == 3:
        return float(mp.sqrt(3)), "大圆正三角形：√3"
    if N == 4:
        return float(3 * mp.sqrt(6) / 2), "正四面体：3√6/2"
    if N == 6:
        return float(6 * mp.sqrt(2) + 1.5), "正八面体：6√2+3/2"
    if N == 12:
        phi = (1 + mp.sqrt(5)) / 2
        r = mp.sqrt(1 + phi ** 2)
        V = []
        for a in (-1, 1):
            for b in (-phi, phi):
                V.append((0, a, b)); V.append((a, b, 0)); V.append((b, 0, a))
        V = [tuple(x / r for x in v) for v in V]
        E = mp.fsum(1 / mp.sqrt(mp.fsum((V[i][k] - V[j][k]) ** 2 for k in range(3)))
                    for i in range(12) for j in range(i + 1, 12))
        return float(E), "正二十面体（精确构造）"
    raise ValueError(N)

# ----------------------------------------------------- 主流程
def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--deg", type=int, default=CFG["DEG"])
    ap.add_argument("--ngrid", type=int, default=CFG["NGRID"])
    ap.add_argument("--seed", type=int, default=CFG["SEED"])
    ap.add_argument("--out", type=str, default=None)
    ap.add_argument("--energies", type=str, default=None)
    ap.add_argument("--no-selftest", action="store_true")
    args = ap.parse_args()
    cfg = dict(CFG)
    cfg.update(DEG=args.deg, NGRID=args.ngrid, SEED=args.seed)
    np.random.seed(cfg["SEED"])               # 固定随机种子（防御性；流水线确定性）

    here = Path(__file__).resolve().parent
    out_path = Path(args.out) if args.out else here / "results" / "lp.json"
    energies_path = (Path(args.energies) if args.energies
                     else here.parents[2] / "thomson-workflow" / "data" / "energies.json")

    t_start = time.time()
    N = cfg["N"]

    # 目标能量：读 energies.json（三源校验值）
    E_star = None
    try:
        with open(energies_path) as f:
            data = json.load(f)
        E_star = float(data["energies"]["9"]["value"])
        src = str(energies_path)
        E_star_hp = data["energies"]["9"]["highPrecision"]
    except Exception as e:                    # 缺文件则用任务书常数（记录在 JSON）
        E_star, src, E_star_hp = 25.759986531, "fallback-constant（energies.json 不可读: %s）" % e, None
        print(f"[warn] energies.json 读取失败（{e}），使用常数 E* = {E_star}", flush=True)

    # ---- 1) LP：找候选多项式
    t0 = time.time()
    lp_val, coef = solve_lp(N, cfg["DEG"], cfg["NGRID"], cfg["LP_TOL"], cfg["SEED"])
    lp_time = time.time() - t0
    print(f"[LP] N={N} deg={cfg['DEG']} ngrid={cfg['NGRID']} -> LP 值 = {lp_val:.12f}（{lp_time:.1f}s）", flush=True)

    # ---- 2) 有理化（向下舍入到 2^-64 网格；k>=1 钳非负）
    fr = [dyadic_floor(x, cfg["ROUND_BITS"]) for x in coef]
    n_clamped = sum(1 for k, c in enumerate(fr[1:], 1) if c == 0 and coef[k] != 0.0)
    assert all(c >= 0 for c in fr[1:]), "k>=1 的 Legendre 系数必须非负"

    # ---- 3) 精确幂基（并回归自检：与 numpy 的 Legendre 求值一致）
    LEG = legendre_power_basis(cfg["DEG"])
    power = [F0] * (cfg["DEG"] + 1)
    for k, c in enumerate(fr):
        for j, p in enumerate(LEG[k]):
            power[j] += c * p
    for tchk in (-0.866, -0.5, -0.113, 0.0, 0.31, 0.77, 0.996):
        v_exact = float(horner(power, Fraction(tchk)))
        v_ref = float(L.legval(tchk, [float(c) for c in fr]))
        if abs(v_exact - v_ref) > 1e-9 * max(1.0, abs(v_ref)):
            print(f"[bug] 幂基转换与 Legendre 求值不一致 @t={tchk}: {v_exact} vs {v_ref}")
            sys.exit(1)

    # ---- 4) 认证扫描
    cert = certify(fr, power, cfg)
    print(f"[cert] 扫描：{cert['n_eval']} 叶（pass {cert['n_pass']}，到宽限 {cert['n_leaf']}），"
          f"M = sup(f-phi) 上界 = {float(cert['M']):.3e}，尾部 ok = {cert['tail_ok']}（{cert['sweep_time']:.1f}s）")
    if not cert["tail_ok"]:
        print(f"[cert] 尾部检查失败：bound = {float(cert['tail_bound']):.3e}", flush=True)
        sys.exit(1)

    # ---- 5) 平移 η，得严格证书与下界
    eta = cert["M"] + cfg["ETA_MARGIN"]
    c0_hat = fr[0] - eta
    f1_hat = sum(fr) - eta                    # f̂(1) = Σ ĉ_k（P_k(1)=1），精确
    B_exact = Fraction(N * N * c0_hat - N * f1_hat, 2)
    scale = 10 ** cfg["REPORT_DEC"]
    i_rep = B_exact.numerator * scale // B_exact.denominator   # floor
    bound = i_rep / scale                                        # 报告值（<= B_exact）

    # ---- 6) 自检：LP 对已知 N 的紧合校准
    selftest = []
    if not args.no_selftest:
        for Nt in cfg["SELFTEST"]:
            Et, desc = exact_E(Nt)
            lpt, _ = solve_lp(Nt, cfg["DEG"], cfg["NGRID"], cfg["LP_TOL"], cfg["SEED"])
            ok = (lpt <= Et + 5e-6) and (lpt >= Et - 5.0)
            selftest.append(dict(N=Nt, lp=round(lpt, 9), E=Et, desc=desc,
                                 tight=round(Et - lpt, 9), ok=bool(ok)))
            print(f"[selftest] N={Nt:2d}: LP={lpt:.9f}  E={Et:.9f}  E-LP={Et-lpt:.2e}  {'OK' if ok else 'FAIL'}", flush=True)
        if any(not s["ok"] for s in selftest):
            print("[selftest] 存在校准失败（LP 值超出真值 5e-6 或异常低）——流水线有 bug，拒绝出界")
            sys.exit(1)

    gap = E_star - bound
    print(f"[result] 认证下界 B = {bound:.9f}（精确值 {B_exact}）", flush=True)
    print(f"[result] E* = {E_star:.9f}（{src}）", flush=True)
    print(f"[result] 差距 E* − B = {gap:.9f}", flush=True)

    # ---- 7) 任务规定的合法性断言
    if not (0 < bound <= E_star + 1e-6):
        print(f"[assert] 违反 0 < bound <= E* + 1e-6：bound = {bound!r}, E* = {E_star!r}", flush=True)
        sys.exit(1)

    # ---- 8) 落盘
    result = {
        "kind": "lp",
        "script": "lp_bound.py",
        "timestamp": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "target": {"N": N, "E_star": E_star, "E_star_highPrecision": E_star_hp, "source": src},
        "bound": bound,
        "bound_exact": f"{B_exact.numerator}/{B_exact.denominator}",
        "gap_to_E_star": gap,
        "lp_raw": lp_val,
        "certification_loss": lp_val - bound,
        "certificate": {
            "potential": "phi(t) = (2-2t)^(-1/2)",
            "form": "f(t) = Σ_{k=0}^{d} c_k P_k(t)，条件 c_k>=0 (k>=1) 且 f<=phi 于 [-1,1)",
            "bound_formula": "E >= (N^2 c_0 - N f(1)) / 2（P_k 在 S^2 正定，加法定理）",
            "degree": cfg["DEG"],
            "coeffs_legendre_exact": [f"{c.numerator}/{c.denominator}" for c in
                                      ([c0_hat] + fr[1:])],
            "eta_exact": f"{eta.numerator}/{eta.denominator}",
            "M_sup_f_minus_phi_exact": f"{cert['M'].numerator}/{cert['M'].denominator}",
            "checks": {
                "coeffs_nonneg_k_ge_1": True,
                "f_le_phi_certified_exact_rational": True,
                "taylor_tail_rigorous": True,
                "tail_interval_check": bool(cert["tail_ok"]),
            },
        },
        "method": {
            "name": "Yudin/Delsarte 两点 LP 界（对偶 = 插值多项式 minorant）",
            "seed": cfg["SEED"],
            "grid_points": cfg["NGRID"],
            "grid_range": "[-1, 1-1e-9] 均匀",
            "solver": "scipy.optimize.linprog(method='highs')",
            "primal_feasibility_tolerance": cfg["LP_TOL"],
            "round_bits": cfg["ROUND_BITS"],
            "code_version": code_version(),
            "certification": "精确有理算术（Fraction + math.isqrt）；LP 解仅作候选，证书不信任浮点",
            "sweep_first_level_intervals": cfg["FIRST_LEVEL"],
            "sweep_min_width": f"2^-{cfg['W_MIN_EXP']}",
            "taylor_exact_terms": cfg["TAYLOR_K"] + 1,
            "phi_bound_resolution": f"2^-{cfg['PHI_P']}",
            "eta_margin": f"2^-46",
        },
        "verification": {
            "sweep_leaves_evaluated": cert["n_eval"],
            "sweep_leaves_pass": cert["n_pass"],
            "sweep_leaves_at_width_limit": cert["n_leaf"],
            "sweep_time_s": round(cert["sweep_time"], 2),
            "worst_leaf": [float(cert["worst"][0]), float(cert["worst"][1])] if cert["worst"] else None,
            "tail_bound": float(cert["tail_bound"]),
        },
        "selftest": selftest,
        "runtime_s": round(time.time() - t_start, 1),
        "repro": "python3 numerics/bounds/lp_bound.py",
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(result, f, ensure_ascii=False, indent=2)
    print(f"[out] 已写入 {out_path}", flush=True)
    print(f"[done] 用时 {result['runtime_s']}s", flush=True)

if __name__ == "__main__":
    main()
