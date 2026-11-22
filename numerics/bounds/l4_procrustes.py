#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""l4_procrustes.py — L4（账本 L5 位）Gram→构型 Procrustes 刚性常数（区间算术）。

GAP-REPORT Round 4 引理账本 L5「Gram→构型：PSD Procrustes 不等式 + 常数（依赖
G_TTP 谱）」的交付：对 TTP 构型 X（triCapPrism(z*)，z* 取 local_min.json 严格隔离
区间的最坏情形），给出区间算术（纯 Fraction 端点）的刚性常数：

  定理（内积口径）：X 固定，S = XᵀX 特征值 λ₁≥λ₂≥λ₃>0。设 Y ∈ R^{9×3} 行单位，
  按固定标号 |⟨y_i,y_j⟩ − ⟨x_i,x_j⟩| ≤ δ (∀i<j)。记 η = ‖G_Y−G_X‖_F ≤ √72·δ，
  β := λ₁·η/λ₃²。若 β ≤ min(1/2, √λ₃/(2σ₁))（σ_i = √λ_i），则

      d_P(X,Y) := min_{Q∈O(3)} ‖X − YQ‖_F ≤ (σ₁³/λ₃² + 2/σ₃)·η ≤ C·δ，
      C = √72·(σ₁³/λ₃² + 2/σ₃)。

  距离口径：|‖x_i−x_j‖−‖y_i−y_j‖| ≤ δ ⇒ |Δ内积| = |Δd²|/2 = |Δd|(d+d')/2 ≤ 2δ
  （弦距 ≤ 2）⇒ 常数 2C。重排：前提在重排 π 下成立时，对 Yπ 应用即得
  min_{Q,π} ‖X − YπQ‖ ≤ C·δ（模 O(3)×S₉）。

证明（脚本内全部步骤；机器验证的部分＝λ 界的区间 Sylvester 判定）：
  1. D := Y−X ⇒ E := G_Y−G_X = XDᵀ+DXᵀ+DDᵀ，E 对角恒 0（双侧行单位）。
  2. 投影分解：D_∥ = XA（A 3×3），D_⊥ 列 ⊥ col(X)（XᵀD_⊥ = 0），P₀ = XS⁻¹Xᵀ。
  3. 混合块：P₀E(I−P₀) = XD_⊥ᵀ + D_∥D_⊥ᵀ，而
     ‖XD_⊥ᵀ‖²_F = tr(S·D_⊥ᵀD_⊥) ≥ λ₃·‖D_⊥‖²_F（A⪰λ₃I, B⪰0 ⇒ tr(AB)≥λ₃tr(B)）
     ⇒ (σ₃ − ‖D_∥‖_F)·‖D_⊥‖_F ≤ ‖E‖_F = η。
  4. 平行块：XᵀEX = S·B·S，B := A+Aᵀ+AAᵀ = (I+A)(I+A)ᵀ−I = S⁻¹(XᵀEX)S⁻¹，
     ‖B‖_F ≤ ‖XᵀEX‖_F/λ₃² ≤ λ₁η/λ₃² = β。
  5. 旋转规范（d_P 本身 min 掉 O(3)）：取右极分解 I+A = W·R（β<1 ⇒ 可逆），
     W = ((I+A)(I+A)ᵀ^{1/2} 对称 PSD，特征值 = I+A 的奇异值 ∈ [√(1−β),√(1+β)]，
     故 ‖W−I‖₂ ≤ 1−√(1−β) ≤ β。则 YR = XW + D_⊥R，‖X−YR‖ ≤ σ₁β + ‖D_⊥‖。
  6. σ₁β ≤ σ₃/2 时 ‖D_⊥‖ ≤ η/(σ₃−σ₁β) ≤ 2η/σ₃，
     d_P ≤ ‖X−YR‖ ≤ σ₁β + 2η/σ₃ = (σ₁³/λ₃²)η + (2/σ₃)η。∎

  注意：这是【线性】Lipschitz 常数（账本 L5 原设想的 C√η 是谱秩亏/仅 PSD 序信息
  下的 ½-Hölder 现象；σ₃(TTP)>0 时线性严格更强）。

严格化方式：X 未知精确值，z* ∈ [z_lo,z_hi]（local_min.json 严格区间，精确有理端点）。
区间实现：三角常数精确（1, −1/2, ±√3/2 有理区间），ρ = √(1−z²) 区间牛顿有理包，
S(z) = XᵀX 区间矩阵；λ₃ ≥ l₃（S−l₃I 全 z 箱 Sylvester 正定）、λ₁ ≤ u₁
（u₁I−S 正定）均以精确 Fraction 区间判定；C 与 δ_max 只用安全向（u₁↑ / l₃↓ /
√ 有理上界↑、下界↓）。全部算术为 Fraction——无浮点进入严格部分。

用法（thomson-n9 下）：
  numerics/.venv/bin/python numerics/bounds/l4_procrustes.py             # 主链 + results/l4.json
  numerics/.venv/bin/python numerics/bounds/l4_procrustes.py --selftest  # 负对照（必须触发）

诚实口径：λ 界与常数是严格数值层（Fraction 区间）；定理证明为上述书面推导
（未过 Lean）；monte-carlo 比率扫描与 Gram 谱为 float advisory（标注 advisory）。
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
NUM = HERE.parent
sys.path.insert(0, str(NUM))

from family import tri_cap_prism                       # noqa: E402  (float advisory 用)

LOCAL_MIN = HERE / "results" / "local_min.json"
OUT = HERE / "results" / "l4.json"
F0, F1 = Fraction(0), Fraction(1)
N_PAIR_OFFDIAG = 72                                    # 9×9 对称零对角 Gram 偏差矩阵的非零元数
SQRT72_MARGIN_BITS = 200                               # 有理平方根包的精度（bit）


def log(msg: str) -> None:
    print(msg, flush=True)


def fail(msg: str) -> None:
    print(f"[FAIL] {msg}", flush=True)
    sys.exit(1)


def code_version() -> str:
    try:
        return subprocess.check_output(
            ["git", "describe", "--always", "--dirty"], cwd=str(REPO),
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown(non-git)"


# ============================================================ 有理区间算术
def sqrt_rat(q: Fraction, side: str) -> Fraction:
    """√q 的有理下界（'lo'）/上界（'hi'），整数 Newton（math.isqrt），q ≥ 0。"""
    import math
    if q < 0:
        raise ValueError("sqrt of negative")
    if q == 0:
        return F0
    p = SQRT72_MARGIN_BITS
    num, den = q.numerator, q.denominator
    if side == "lo":
        n = math.isqrt((num << (2 * p)) // den)
        return Fraction(n, 1 << p)
    n = math.isqrt((num << (2 * p)) // den + 1) + 1
    return Fraction(n, 1 << p)


class Iv:
    """Fraction 端点闭区间 [lo, hi]（区间运算保守外扩，端点精确）。"""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        self.lo, self.hi = min(lo, hi), max(lo, hi)

    def __add__(a, b):
        return Iv(a.lo + b.lo, a.hi + b.hi)

    def __sub__(a, b):
        return Iv(a.lo - b.hi, a.hi - b.lo)

    def __mul__(a, b):
        vals = (a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi)
        return Iv(min(vals), max(vals))

    def __neg__(a):
        return Iv(-a.hi, -a.lo)

    def widen(a):
        return (a.lo, a.hi)

    def __repr__(a):
        return f"[{float(a.lo):.12f},{float(a.hi):.12f}]"


def iv_sqrt(a: Iv) -> Iv:
    return Iv(sqrt_rat(a.lo, "lo") if a.lo > 0 else F0, sqrt_rat(a.hi, "hi"))


# ============================================================ TTP 区间构型
R3LO, R3HI = sqrt_rat(Fraction(3), "lo"), sqrt_rat(Fraction(3), "hi")
IV_R3 = Iv(R3LO, R3HI)


def ttp_interval(zbox: tuple[Fraction, Fraction]):
    """tri_cap_prism(z) 的 9×3 区间矩阵（三角常数精确；ρ=√(1−z²) 区间）。

    与 numerics/family.py tri_cap_prism 同构：顶/底三角半径 ρ=√(1−z²)，
    角 2πk/3；赤道三帽半径 1，角 π/3+2πk/3。常数全部精确（1, −1/2, ±1/2，
    ±√3/2 用 √3 的有理区间）。
    """
    zl, zh = zbox
    z = Iv(zl, zh)
    rho = iv_sqrt(Iv(F1 - zh * zh, F1 - zl * zl))      # 1−z² 于正区间上递减
    h = rho * (IV_R3 * Iv(Fraction(1, 2)))             # ρ·(√3/2)
    rows = []
    for sgn in (F1, -F1):                              # 上三角、下三角（z 坐标 ±z）
        sz = z if sgn == 1 else -z
        rows.append([rho, Iv(F0), sz])                             # k=0: (1, 0)
        rows.append([rho * Iv(Fraction(-1, 2)), h, sz])            # k=1: (−1/2, √3/2)
        rows.append([rho * Iv(Fraction(-1, 2)), -h, sz])           # k=2: (−1/2, −√3/2)
    h3 = IV_R3 * Iv(Fraction(1, 2))                    # √3/2
    rows.append([Iv(Fraction(1, 2)), h3, Iv(F0)])                  # 帽 k=0: 60°
    rows.append([Iv(-F1), Iv(F0), Iv(F0)])                         # 帽 k=1: 180°
    rows.append([Iv(Fraction(1, 2)), -h3, Iv(F0)])                 # 帽 k=2: 300°
    return rows


def gram_S(rows):
    """S = XᵀX 的 3×3 区间矩阵（rows = 9×3 的 Iv）。"""
    S = [[Iv(F0) for _ in range(3)] for _ in range(3)]
    for r in rows:
        for i in range(3):
            for j in range(3):
                S[i][j] = S[i][j] + r[i] * r[j]
    return S


def interval_sylvester_pd(M) -> bool:
    """3×3 对称区间矩阵全实例正定？Sylvester：全部顺序主子式区间下端 > 0。"""
    def det2(a, b, c, d):
        return a * d - b * c

    def det3(m):
        return (m[0][0] * det2(m[1][1], m[1][2], m[2][1], m[2][2])
                - m[0][1] * det2(m[1][0], m[1][2], m[2][0], m[2][2])
                + m[0][2] * det2(m[1][0], m[1][1], m[2][0], m[2][1]))

    if not (M[0][0].lo > 0):
        return False
    d2 = det2(M[0][0], M[0][1], M[0][1], M[1][1])
    if not (d2.lo > 0):
        return False
    d3 = det3(M)
    return d3.lo > 0


def certify_lambdas(S_iv, lam3_float, lam1_float):
    """λ₃ ≥ l₃ 与 λ₁ ≤ u₁（区间 Sylvester，安全向搜索）。"""
    l3 = None
    t = Fraction(int(lam3_float * 10 ** 6), 10 ** 6)       # 从 float 值起向下试探
    for k in range(200):
        cand = t - Fraction(k, 10 ** 6)
        M = [[S_iv[i][j] - (Iv(cand) if i == j else Iv(F0)) for j in range(3)]
             for i in range(3)]
        if interval_sylvester_pd(M):
            l3 = cand
            break
    u1 = None
    t = Fraction(int(lam1_float * 10 ** 6), 10 ** 6)
    for k in range(200):
        cand = t + Fraction(k, 10 ** 6)
        M = [[(Iv(cand) if i == j else Iv(F0)) - S_iv[i][j] for j in range(3)]
             for i in range(3)]
        if interval_sylvester_pd(M):
            u1 = cand
            break
    return l3, u1


# ============================================================ 数值 advisory
def proof_identity_checks(z_mid: float):
    """证明步骤的数值恒等式核对（float，随机扰动上各步残差应 ~1e-15）。"""
    import numpy as np
    rng = np.random.default_rng(20261006)
    X = tri_cap_prism(z_mid)
    worst = {}
    for _ in range(5):
        D = 10 ** rng.uniform(-5, -2) * rng.standard_normal((9, 3))
        Y = X + D
        Yn = Y / np.linalg.norm(Y, axis=1, keepdims=True)   # 行单位化的实现
        D = Yn - X
        E = Yn @ Yn.T - X @ X.T
        S = X.T @ X
        P0 = X @ np.linalg.inv(S) @ X.T
        A = np.linalg.inv(S) @ (X.T @ D)
        Dpar = X @ A
        Dperp = D - Dpar
        res = {
            "E_def": np.linalg.norm(E - (X @ D.T + D @ X.T + D @ D.T)),
            "mixed_block": np.linalg.norm(
                P0 @ E @ (np.eye(9) - P0) - (X @ Dperp.T + Dpar @ Dperp.T)),
            "off_block": np.linalg.norm(
                (np.eye(9) - P0) @ E @ (np.eye(9) - P0) - Dperp @ Dperp.T),
            "parallel_block": np.linalg.norm(
                X.T @ E @ X - S @ (A + A.T + A @ A.T) @ S),
            "Xdperp_norm": abs(np.sum((X @ Dperp.T) ** 2)
                               - np.trace(S @ Dperp.T @ Dperp)),
            "procrustes_dP": abs(
                np.linalg.norm(X - Yn @ (lambda M: np.linalg.svd(M)[0]
                 @ np.linalg.svd(M)[2])(Yn.T @ X)) ** 2
                - (18.0 - 2.0 * np.linalg.svd(Yn.T @ X, compute_uv=False).sum())),
        }
        for k, v in res.items():
            worst[k] = max(worst.get(k, 0.0), float(v))
    scale = max(worst.values())
    if not (scale < 1e-10):
        fail(f"证明恒等式数值核对失败：max 残差 {scale:.2e}")
    return dict(max_residual_per_step=worst, trials=5, note="float 数值核对（advisory）")


def numeric_advisory(z_mid: float, C_float: float, delta_max_float: float):
    """float 检查：Procrustes 比率 monte-carlo（正检）+ Gram 谱。"""
    import numpy as np
    rng = np.random.default_rng(20261005)
    X = tri_cap_prism(z_mid)
    G = X @ X.T
    lam = np.linalg.eigvalsh(X.T @ X)
    trials, max_ratio, max_delta = 0, 0.0, 0.0
    for _ in range(300):
        scale = 10 ** rng.uniform(-6, -1.3)
        Qr = np.linalg.qr(rng.standard_normal((3, 3)))[0]
        Y = X @ Qr + scale * rng.standard_normal((9, 3))
        Y /= np.linalg.norm(Y, axis=1, keepdims=True)      # 行单位 ⇒ E 对角 = 0
        Gy = Y @ Y.T
        delta = float(np.max(np.abs(Gy - G)))              # 含对角（恰为 0）
        if delta <= 0 or delta > delta_max_float:
            continue
        M = Y.T @ X                                        # min_Q ‖X−YQ‖：Σσ(M)
        sig = np.linalg.svd(M, compute_uv=False).sum()
        d_p = float(np.sqrt(max(0.0, 18.0 - 2.0 * sig)))
        trials += 1
        max_ratio = max(max_ratio, d_p / delta)
        max_delta = max(max_delta, delta)
        if d_p > C_float * delta:
            fail(f"monte-carlo 违反：d_P={d_p:.3e} > C·δ={C_float * delta:.3e}")
    return dict(lambdas_float=[float(v) for v in lam],
                monte_carlo=dict(trials=trials, max_ratio=float(max_ratio),
                                 max_delta_tested=float(max_delta),
                                 all_within_C=True,
                                 note="float advisory（非证明）；d_P = sqrt(18−2Σσ(YᵀX))"))


# ============================================================ 负对照
def run_selftest(S_iv, delta_max_float, z_mid):
    """三个负对照，全部必须按预期触发（触发 = 检查正确地拒绝/检出）。"""
    out = {}
    # NC1：秩亏构型（z=0 全赤道化：S₃₃ = 0 ⇒ λ₃ = 0）——λ₃>0 认证必须失败
    rows0 = ttp_interval((F0, F0))
    S0 = gram_S(rows0)
    M0 = [[S0[i][j] - (Iv(Fraction(1, 100)) if i == j else Iv(F0)) for j in range(3)]
          for i in range(3)]
    trig1 = not interval_sylvester_pd(M0)
    out["NC1_rank_deficient_planar"] = dict(
        setup="z-box=[0,0]（顶/底三角塌到赤道）：S₃₃ = 0 ⇒ λ₃ = 0",
        claim="λ₃ ≥ 1/100 的区间 Sylvester 认证",
        triggered=bool(trig1),
        expected="必须拒绝（σ₃=0 时线性常数定理不适用——σ₃>0 是实质前提）")
    # NC2：认证器有齿——把 t 抬到 λ₁ 之上，S−tI 正定判定必须失败
    Mbad = [[S_iv[i][j] - (Iv(Fraction(4, 1)) if i == j else Iv(F0))
             for j in range(3)] for i in range(3)]
    trig2 = not interval_sylvester_pd(Mbad)
    out["NC2_certifier_teeth"] = dict(
        setup="t = 4 > λ₁(S) ≈ 3.01：S − 4I 必非正定",
        claim="区间 Sylvester 正定判定",
        triggered=bool(trig2), expected="必须拒绝")
    # NC3：标号前提失效——非对称重排的 Gram 偏差必须超出适用 δ 范围
    import numpy as np
    X = tri_cap_prism(z_mid)
    G = X @ X.T
    perm = list(range(9))
    perm[0], perm[8] = perm[8], perm[0]                    # 帽 ↔ 顶三角顶点
    Gp = G[np.ix_(perm, perm)]
    d_perm = float(np.max(np.abs(Gp - G)))
    trig3 = d_perm > delta_max_float
    out["NC3_labeling_premise"] = dict(
        setup="Y = X 重排（帽↔顶三角顶点）：固定标号下 Gram 偏差 δ_perm",
        delta_perm=d_perm, delta_max=delta_max_float,
        triggered=bool(trig3),
        expected="δ_perm 须 > δ_max（前提不满足 ⇒ 定理不适用；模重排商掉后 d_P=0）",
        note="d_P(模 O(3)×S₉) = 0（同一构型），验证商掉重排的语义")
    ok = trig1 and trig2 and trig3
    for k, v in out.items():
        log(f"[nc   ] {k}: triggered={v['triggered']}（{v['expected']}）")
    if not ok:
        fail("负对照未全部触发")
    return out


# ============================================================ 主链
def main() -> None:
    ap = argparse.ArgumentParser(description="L4 Procrustes 刚性常数（区间算术）")
    ap.add_argument("--selftest", action="store_true",
                    help="只跑负对照（全部必须触发）")
    args = ap.parse_args()
    t0 = time.time()

    lm = json.loads(LOCAL_MIN.read_text())
    zl_s, zh_s = lm["zStarIntervalMpmath"].strip("[]").split(", ")
    zbox = (Fraction(zl_s), Fraction(zh_s))
    z_mid = float((zbox[0] + zbox[1]) / 2)

    rows = ttp_interval(zbox)
    S_iv = gram_S(rows)
    # 区间正确性抽查：float S(z_mid) 落在区间内（float advisory 值，宽度余量 ~1e-6）
    Xf = tri_cap_prism(z_mid)
    Sf = Xf.T @ Xf
    for i in range(3):
        for j in range(3):
            v = Fraction(float(Sf[i][j]))
            if not (S_iv[i][j].lo <= v <= S_iv[i][j].hi):
                fail(f"区间包含检查失败：S[{i}][{j}]={float(v)} ∉ {S_iv[i][j]}")
    lam1_f = 3.0 * (1 - z_mid ** 2) + 1.5                 # D3h 解析谱（advisory 初值）
    lam3_f = 6 * z_mid ** 2
    l3, u1 = certify_lambdas(S_iv, lam3_f, lam1_f)
    if l3 is None or u1 is None:
        fail("λ 界区间认证失败（l₃/u₁ 未找到）")
    log(f"[lam  ] λ₃ ≥ {float(l3):.9f}（解析 advisory {lam3_f:.9f}）；"
        f"λ₁ ≤ {float(u1):.9f}（advisory {lam1_f:.9f}）——区间 Sylvester 全 z 箱 ✓")

    s1_up = sqrt_rat(u1, "hi")                            # σ₁ = √λ₁ ≤ s1_up
    s3_dn = sqrt_rat(l3, "lo")                            # σ₃ = √λ₃ ≥ s3_dn
    sqrt72 = sqrt_rat(Fraction(72), "hi")
    eta_of_delta = sqrt72                                 # η ≤ √72·δ（72 非对角元）
    C_inner = u1 * s1_up / (l3 * l3) + Fraction(2) / s3_dn
    C = eta_of_delta * C_inner
    # 适用范围：β = λ₁η/λ₃² ≤ min(1/2, σ₃/(2σ₁))，η ≤ √72δ
    half = Fraction(1, 2)
    reg2 = s3_dn / (2 * s1_up)
    reg = min(half, reg2)
    delta_max = reg * l3 * l3 / (eta_of_delta * u1)
    C_dist = 2 * C
    log(f"[const] C = √72·(σ₁³/λ₃² + 2/σ₃) = {float(C):.6f}；"
        f"δ_max = {float(delta_max):.6f}；距离口径 C_dist = 2C = {float(C_dist):.6f}")

    adv = numeric_advisory(z_mid, float(C), float(delta_max))
    log(f"[adv  ] monte-carlo：{adv['monte_carlo']['trials']} 试次全过，"
        f"max d_P/δ = {adv['monte_carlo']['max_ratio']:.3f} < C（advisory）")
    proof_chk = proof_identity_checks(z_mid)
    log(f"[proof] 推导恒等式数值核对：max 残差 "
        f"{max(proof_chk['max_residual_per_step'].values()):.2e}（5 试次 × 6 步）")

    nc = run_selftest(S_iv, float(delta_max), z_mid) if args.selftest else None

    doc = dict(
        kind="n9-l4-procrustes",
        script="bounds/l4_procrustes.py",
        code_version=code_version(),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        theorem=dict(
            statement=(
                "X = TTP（行单位 9×3），S = XᵀX 谱 λ₁≥λ₂≥λ₃>0，σᵢ=√λᵢ。"
                "Y 行单位且固定标号 |⟨y_i,y_j⟩−⟨x_i,x_j⟩| ≤ δ (∀i<j)。"
                "η=‖G_Y−G_X‖_F ≤ √72·δ，β=λ₁η/λ₃²。"
                "β ≤ min(1/2, √λ₃/(2σ₁)) ⇒ min_{Q∈O(3)}‖X−YQ‖_F "
                "≤ (σ₁³/λ₃²+2/σ₃)·η ≤ C·δ"),
            metric=("R²⁷ 弦距离 sqrt(Σᵢ‖x_i−y_i‖²)＝9×3 Frobenius（与 L6 管半径 "
                    "r_tube 同度量）；商掉 O(3)（d_P 定义）与 S₉（前提对某重排成立"
                    "时对该重排应用）"),
            premise_variants=dict(
                inner_product_delta=dict(C="C（本定理）"),
                chord_distance_delta=dict(
                    C="2C", why="|Δt| = |Δd²|/2 = |Δd|(d+d')/2 ≤ 2δ（弦距 ≤ 2）")),
            proof=[
                "D=Y−X ⇒ E=G_Y−G_X=XDᵀ+DXᵀ+DDᵀ，E 对角恒 0",
                "D_∥=XA、D_⊥⊥col(X)，P₀=XS⁻¹Xᵀ；混合块 P₀E(I−P₀)=XD_⊥ᵀ+D_∥D_⊥ᵀ",
                "‖XD_⊥ᵀ‖²_F=tr(S·D_⊥ᵀD_⊥) ≥ λ₃‖D_⊥‖²_F ⇒ (σ₃−‖D_∥‖)‖D_⊥‖ ≤ η",
                "XᵀEX=S·B·S，B=(I+A)(I+A)ᵀ−I=S⁻¹(XᵀEX)S⁻¹，‖B‖ ≤ λ₁η/λ₃² = β",
                "右极分解 I+A=W·R：W=((I+A)(I+A)ᵀ)^{1/2} 对称，奇异值∈[√(1−β),√(1+β)]"
                " ⇒ ‖W−I‖₂ ≤ 1−√(1−β) ≤ β；YR=XW+D_⊥R ⇒ ‖X−YR‖ ≤ σ₁β+‖D_⊥‖",
                "σ₁β ≤ σ₃/2 ⇒ ‖D_⊥‖ ≤ 2η/σ₃ ⇒ d_P ≤ ‖X−YR‖ ≤ (σ₁³/λ₃²+2/σ₃)η ∎"],
            note=("线性 Lipschitz（账本 L5 设想的 C√η 为 ½-Hölder 口径：σ₃>0 时线性"
                  "严格更强；σ₃→0 退化为 Hölder 是定理前提 σ₃>0 的实质内容")),
        ttp_interval=dict(
            z_box=[str(zbox[0]), str(zbox[1])],
            z_box_source="results/local_min.json zStarIntervalMpmath（严格隔离区间）",
            z_box_width=float(zbox[1] - zbox[0]),
            S_interval=[[f"[{S_iv[i][j].lo},{S_iv[i][j].hi}]"
                         for j in range(3)] for i in range(3)],
            method=("纯 Fraction 区间（三角常数精确；ρ=√(1−z²) 整数 Newton 有理包）；"
                    "λ 界＝区间 Sylvester 顺序主子式（3×3 区间行列式，保守外扩）"),
            lambda3_lower_exact=str(l3), lambda3_lower_float=float(l3),
            lambda1_upper_exact=str(u1), lambda1_upper_float=float(u1),
            sigma1_upper=str(s1_up), sigma3_lower=str(s3_dn)),
        constants=dict(
            C_exact=str(C), C_float=float(C),
            C_inner_Frobenius_exact=str(C_inner),
            C_inner_Frobenius_float=float(C_inner),
            C_chord_distance_exact=str(C_dist), C_chord_distance_float=float(C_dist),
            delta_max_exact=str(delta_max), delta_max_float=float(delta_max),
            regime=("β = λ₁η/λ₃² ≤ min(1/2, σ₃/(2σ₁))，η ≤ √72·δ；"
                    "即 δ ∈ (0, δ_max] 时 d_P ≤ C·δ（内积口径）/ ≤ 2C·δ（距离口径）"),
            eta_bound="√72（9×9 对称零对角偏差矩阵 72 个非零元，逐元 ≤ δ）"),
        numeric_advisory=adv,
        proof_identity_checks=proof_chk,
        selftest=nc if nc else "not run（--selftest 启用）",
        scope=("严格数值层：λ 界与常数为纯 Fraction 区间算术（区间端点精确、保守外扩）；"
               "定理证明为书面推导（上述 proof 步骤，未过 Lean 内核）；monte-carlo 与"
               " Gram 谱为 float advisory"),
        wall_s=round(time.time() - t0, 1),
    )
    OUT.write_text(json.dumps(doc, ensure_ascii=False, indent=1))
    print(json.dumps({
        "C": float(C), "C_chord": float(C_dist),
        "delta_max": float(delta_max), "lambda3_lower": float(l3),
        "lambda1_upper": float(u1),
        "selftest_negative_controls_triggered": (nc is not None and all(
            v["triggered"] for v in nc.values())) if nc else "not run",
        "out": str(OUT.relative_to(REPO)), "wall_s": doc["wall_s"]},
        ensure_ascii=False, indent=1))
    log(f"[done ] L4 完成：C = {float(C):.6f}（δ ≤ {float(delta_max):.6f}）；"
        f"写入 {OUT.relative_to(REPO)}；exit 0")


if __name__ == "__main__":
    main()
