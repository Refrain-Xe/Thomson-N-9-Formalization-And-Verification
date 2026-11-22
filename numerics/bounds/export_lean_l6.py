#!/usr/bin/env python3
"""export_lean_l6.py — Self-verifying generator for ThomsonN9/StageB/LocalMinL6Data.lean.

Computes:
  1. Tight rational isolation [zStarLo, zStarHi] of width 10^-11 inside [TableB5Data.zLo, zHi],
     with 20-digit rational square-root envelopes for sqrt(3), rho=sqrt(1-z^2), sqrt(3+z^2),
     sqrt(2+2*rho), sqrt(2-rho) certifying critGap(zStarLo) < 0 < critGap(zStarHi) and
     E_family(z*) <= E_ttp_hi.
  2. Exact scaled-integer (S_iv = 10^6) interval bounds for all 15 scalar parameters of the
     27x27 penalized Bregman Hessian H_pen(z*) at tau_cap = 1/200, alpha = 1/100, K_norm = 10, K_rot = 5.
  3. Exact rational/integer 27x27 matrix H_rat and its Cholesky factor C_27 for H_rat - (1/25)*I_27,
     pre-verified in Python and emitted with `decide +kernel` certificates in LocalMinL6Data.lean.
"""
from __future__ import annotations

import math
from fractions import Fraction
from pathlib import Path

import mpmath as mp

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
OUT = REPO / "formal" / "lean" / "ThomsonN9" / "StageB" / "LocalMinL6Data.lean"

mp.mp.dps = 80

E_TTP_HI_NUM = 257599865312698317
E_TTP_HI_DEN = 10000000000000000
E_TTP_HI = Fraction(E_TTP_HI_NUM, E_TTP_HI_DEN)

# z* = 0.7036483958041317757777523324628161212489...
Z_LO = Fraction(703648395804131775, 10**18)
Z_HI = Fraction(703648395804131776, 10**18)


def floor_sqrt_rat(q: Fraction, den: int) -> Fraction:
    """Return rational r = floor(sqrt(q) * den) / den with r^2 <= q."""
    # r^2 <= q  <=>  r_num^2 * q.denominator <= q.numerator * den^2
    num = math.isqrt((q.numerator * den * den) // q.denominator)
    while (num + 1) * (num + 1) * q.denominator <= q.numerator * den * den:
        num += 1
    while num * num * q.denominator > q.numerator * den * den:
        num -= 1
    r = Fraction(num, den)
    assert r * r <= q
    return r


def ceil_sqrt_rat(q: Fraction, den: int) -> Fraction:
    """Return rational r = ceil(sqrt(q) * den) / den with q <= r^2."""
    num = math.isqrt((q.numerator * den * den) // q.denominator)
    while num * num * q.denominator < q.numerator * den * den:
        num += 1
    r = Fraction(num, den)
    assert q <= r * r
    return r


def nodeOfN(i: int, j: int) -> int:
    if i == j:
        return 9
    if i // 3 == j // 3:
        return 2 if i // 3 == 2 else 4
    if i // 3 == 2:
        return 1 if (i % 3 + 3 - j % 3) % 3 == 1 else 5
    if j // 3 == 2:
        return 1 if (j % 3 + 3 - i % 3) % 3 == 1 else 5
    return 3 if i % 3 == j % 3 else 0


def main():
    D20 = 10 ** 22
    s3_lo = floor_sqrt_rat(Fraction(3), D20)
    s3_hi = ceil_sqrt_rat(Fraction(3), D20)

    # Envelopes on [Z_LO, Z_HI]:
    # rho = sqrt(1 - z^2) is decreasing in z
    rho_lo = floor_sqrt_rat(1 - Z_HI * Z_HI, D20)
    rho_hi = ceil_sqrt_rat(1 - Z_LO * Z_LO, D20)
    # r0 = sqrt(3 + z^2) is increasing in z
    r0_lo = floor_sqrt_rat(3 + Z_LO * Z_LO, D20)
    r0_hi = ceil_sqrt_rat(3 + Z_HI * Z_HI, D20)
    # r1 = sqrt(2 + 2*rho) is increasing in rho
    r1_lo = floor_sqrt_rat(2 + 2 * rho_lo, D20)
    r1_hi = ceil_sqrt_rat(2 + 2 * rho_hi, D20)
    # r5 = sqrt(2 - rho) is decreasing in rho
    r5_lo = floor_sqrt_rat(2 - rho_hi, D20)
    r5_hi = ceil_sqrt_rat(2 - rho_lo, D20)

    # Verify E_family upper bound on [Z_LO, Z_HI]:
    # E_family(z) = 2*s3/rho + s3 + 3/(2*z) + 6/r0 + 12/r5 + 6/r1
    E_hi_env = (2 * s3_hi / rho_lo + s3_hi + Fraction(3, 2) / Z_LO
                + 6 / r0_lo + 12 / r5_lo + 6 / r1_lo)
    assert E_hi_env <= E_TTP_HI, f"E_hi_env={float(E_hi_env):.18f} > E_TTP_HI={float(E_TTP_HI):.18f}"
    print(f"[OK] E_hi_env = {float(E_hi_env):.18f} <= E_TTP_HI = {float(E_TTP_HI):.18f} (margin={float(E_TTP_HI - E_hi_env):.2e})")

    # Pointwise envelopes at Z_LO and Z_HI for critGap(z) = 3*p4^3 - 2*p3^3 - p0^3 - (p5^3 - p1^3)/rho
    # where p0=1/r0, p1=1/r1, p3=1/(2z), p4=1/(s3*rho), p5=1/r5
    def crit_bounds_at(zv: Fraction):
        D = 10 ** 22
        rl = floor_sqrt_rat(1 - zv * zv, D)
        rh = ceil_sqrt_rat(1 - zv * zv, D)
        a0l, a0h = floor_sqrt_rat(3 + zv * zv, D), ceil_sqrt_rat(3 + zv * zv, D)
        a1l, a1h = floor_sqrt_rat(2 + 2 * rl, D), ceil_sqrt_rat(2 + 2 * rh, D)
        a5l, a5h = floor_sqrt_rat(2 - rh, D), ceil_sqrt_rat(2 - rl, D)
        s3l, s3h = floor_sqrt_rat(Fraction(3), D), ceil_sqrt_rat(Fraction(3), D)
        # Upper bound on critGap(zv):
        # max(3*p4^3) - min(2*p3^3) - min(p0^3) - min(p5^3/rho) + max(p1^3/rho)
        p4_hi = 1 / (s3l * rl)
        p4_lo = 1 / (s3h * rh)
        p3 = 1 / (2 * zv)
        p0_lo, p0_hi = 1 / a0h, 1 / a0l
        p5_lo, p5_hi = 1 / a5h, 1 / a5l
        p1_lo, p1_hi = 1 / a1h, 1 / a1l
        ub = 3 * p4_hi**3 - 2 * p3**3 - p0_lo**3 - p5_lo**3 / rh + p1_hi**3 / rl
        lb = 3 * p4_lo**3 - 2 * p3**3 - p0_hi**3 - p5_hi**3 / rl + p1_lo**3 / rh
        return dict(rl=rl, rh=rh, a0l=a0l, a0h=a0h, a1l=a1l, a1h=a1h, a5l=a5l, a5h=a5h,
                    s3l=s3l, s3h=s3h, lb=lb, ub=ub)

    cLo = crit_bounds_at(Z_LO)
    cHi = crit_bounds_at(Z_HI)
    assert cLo["ub"] < 0, f"critGap(Z_LO) ub = {float(cLo['ub'])} >= 0"
    assert cHi["lb"] > 0, f"critGap(Z_HI) lb = {float(cHi['lb'])} <= 0"
    print(f"[OK] critGap(Z_LO) <= {float(cLo['ub']):.3e} < 0 < {float(cHi['lb']):.3e} <= critGap(Z_HI)")

    # Exact rational intervals for the 6 phi(nu_k) and 6 shifted phi(nu_k - 1/200) on [Z_LO, Z_HI]!
    # 2 - 2*nu_k:
    #   k=0: 3 + z^2        -> [3 + Z_LO^2, 3 + Z_HI^2]
    #   k=1: 2 + 2*rho      -> [2 + 2*rho_lo, 2 + 2*rho_hi]
    #   k=2: 3              -> [3, 3]
    #   k=3: 4*z^2          -> [4*Z_LO^2, 4*Z_HI^2]
    #   k=4: 3*(1 - z^2)    -> [3*(1 - Z_HI^2), 3*(1 - Z_LO^2)]
    #   k=5: 2 - rho        -> [2 - rho_hi, 2 - rho_lo]
    d2_box = [
        (3 + Z_LO * Z_LO, 3 + Z_HI * Z_HI),
        (2 + 2 * rho_lo, 2 + 2 * rho_hi),
        (Fraction(3), Fraction(3)),
        (4 * Z_LO * Z_LO, 4 * Z_HI * Z_HI),
        (3 * (1 - Z_HI * Z_HI), 3 * (1 - Z_LO * Z_LO)),
        (2 - rho_hi, 2 - rho_lo),
    ]
    # Shifted by tau_cap = 1/200: 2 - 2*(nu_k - 1/200) = (2 - 2*nu_k) + 1/100
    D12 = 10 ** 12
    phi_box = []
    phi3_box = []
    c5_box = []  # c_k = (3/2) * phi(nu_k - 1/200)^5 = (3/2) / (d2 + 1/100)^(5/2)
    q_shift_box = []  # sqrt(d2 + 1/100) rational envelopes for Lean proofs!
    for lo2, hi2 in d2_box:
        r_lo = floor_sqrt_rat(lo2, D12)
        r_hi = ceil_sqrt_rat(hi2, D12)
        p_lo, p_hi = 1 / r_hi, 1 / r_lo
        phi_box.append((p_lo, p_hi))
        phi3_box.append((p_lo**3, p_hi**3))
        sh_lo2 = lo2 + Fraction(1, 100)
        sh_hi2 = hi2 + Fraction(1, 100)
        sr_lo = floor_sqrt_rat(sh_lo2, D12)
        sr_hi = ceil_sqrt_rat(sh_hi2, D12)
        q_shift_box.append((sr_lo, sr_hi))
        c_lo = Fraction(3, 2) / (sr_hi**5)
        c_hi = Fraction(3, 2) / (sr_lo**5)
        assert c_hi < 1, f"c_hi = {float(c_hi)} >= 1!"
        c5_box.append((c_lo, c_hi))

    # lamP = 2*p4^3 - p3^3 - 2*p0^3, lamC = 2*rho*p5^3 - 2*rho*p1^3 - p2^3
    lamP_lo = 2 * phi3_box[4][0] - phi3_box[3][1] - 2 * phi3_box[0][1]
    lamP_hi = 2 * phi3_box[4][1] - phi3_box[3][0] - 2 * phi3_box[0][0]
    lamC_lo = 2 * rho_lo * phi3_box[5][0] - 2 * rho_hi * phi3_box[1][1] - phi3_box[2][1]
    lamC_hi = 2 * rho_hi * phi3_box[5][1] - 2 * rho_lo * phi3_box[1][0] - phi3_box[2][0]

    # Scaled-integer intervals (scale S_iv = 10^6) for ALL parameters
    S = 10 ** 6
    def to_iv(lo: Fraction, hi: Fraction) -> tuple[int, int]:
        a = math.floor(lo * S)
        b = math.ceil(hi * S)
        assert Fraction(a, S) <= lo and hi <= Fraction(b, S)
        return (a, b)

    iv_z = to_iv(Z_LO, Z_HI)
    iv_rho = to_iv(rho_lo, rho_hi)
    iv_s3 = to_iv(s3_lo, s3_hi)
    iv_s3rho = to_iv(s3_lo * rho_lo, s3_hi * rho_hi)
    iv_phi3 = [to_iv(lo, hi) for lo, hi in phi3_box]
    # Also store (1 - alpha) * c5 = (99/100) * c5 directly!
    iv_ac5 = [to_iv(Fraction(99, 100) * lo, Fraction(99, 100) * hi) for lo, hi in c5_box]
    iv_lamP = to_iv(lamP_lo, lamP_hi)
    iv_lamC = to_iv(lamC_lo, lamC_hi)

    # Exact scaled-integer interval arithmetic (scale S = 10^6 for all basic coords, so product of 2 coords has scale S^2, etc.)
    # Actually, to avoid tracking powers of S inside H_pen_iv, let's do exact division-rounding back to scale S on ivMulS!
    # Wait: if x in [xlo, xhi]/S and y in [ylo, yhi]/S, then x*y in [floor_div(lo, S), ceil_div(hi, S)] / S!
    # That keeps EVERY interval at the SAME scale S = 10^6, with tiny 30-bit integers!!
    def iadd(x, y): return (x[0] + y[0], x[1] + y[1])
    def isub(x, y): return (x[0] - y[1], x[1] - y[0])
    def ineg(x): return (-x[1], -x[0])
    def idiv2(x):
        # exact floor/ceil division by 2
        return (x[0] // 2, (x[1] + 1) // 2)
    def imulS(x, y):
        ps = (x[0]*y[0], x[0]*y[1], x[1]*y[0], x[1]*y[1])
        lo, hi = min(ps), max(ps)
        # floor(lo / S) and ceil(hi / S) in Python:
        qlo = lo // S
        qhi = -((-hi) // S)
        assert qlo * S <= lo and hi <= qhi * S
        return (qlo, qhi)
    def iscale(k, x):
        return (k*x[0], k*x[1]) if k >= 0 else (k*x[1], k*x[0])

    # Build 9x3 coordinate intervals P_iv[i][a] at scale S:
    halfS = S // 2
    P_iv = [
        [iv_rho, (0, 0), iv_z],
        [ineg(idiv2(iv_rho)), idiv2(iv_s3rho), iv_z],
        [ineg(idiv2(iv_rho)), ineg(idiv2(iv_s3rho)), iv_z],
        [iv_rho, (0, 0), ineg(iv_z)],
        [ineg(idiv2(iv_rho)), idiv2(iv_s3rho), ineg(iv_z)],
        [ineg(idiv2(iv_rho)), ineg(idiv2(iv_s3rho)), ineg(iv_z)],
        [(halfS, halfS), idiv2(iv_s3), (0, 0)],
        [(-S, -S), (0, 0), (0, 0)],
        [(halfS, halfS), ineg(idiv2(iv_s3)), (0, 0)],
    ]

    # Build 27x27 H_pen_iv at scale S = 10^6!
    H_iv = [[(0, 0) for _ in range(27)] for _ in range(27)]
    # 1) -(1/2) * lam_i on diagonal
    for i in range(9):
        lam_iv = iv_lamP if i < 6 else iv_lamC
        neg_half = ineg(idiv2(lam_iv))
        for a in range(3):
            H_iv[3*i+a][3*i+a] = iadd(H_iv[3*i+a][3*i+a], neg_half)
    # 2) For each pair i < j: (1/2) phi^3 on (3i+a, 3j+a) & (3j+a, 3i+a), plus ac5 * v v^T
    for i in range(9):
        for j in range(i + 1, 9):
            k = nodeOfN(i, j)
            half_p3 = idiv2(iv_phi3[k])
            for a in range(3):
                H_iv[3*i+a][3*j+a] = iadd(H_iv[3*i+a][3*j+a], half_p3)
                H_iv[3*j+a][3*i+a] = iadd(H_iv[3*j+a][3*i+a], half_p3)
            ac_k = iv_ac5[k]
            # v[3i+a] = P[j][a], v[3j+a] = P[i][a]
            for a in range(3):
                for b in range(3):
                    # (3i+a, 3i+b): ac_k * P_ja * P_jb
                    H_iv[3*i+a][3*i+b] = iadd(H_iv[3*i+a][3*i+b], imulS(ac_k, imulS(P_iv[j][a], P_iv[j][b])))
                    # (3j+a, 3j+b): ac_k * P_ia * P_ib
                    H_iv[3*j+a][3*j+b] = iadd(H_iv[3*j+a][3*j+b], imulS(ac_k, imulS(P_iv[i][a], P_iv[i][b])))
                    # (3i+a, 3j+b): ac_k * P_ja * P_ib
                    H_iv[3*i+a][3*j+b] = iadd(H_iv[3*i+a][3*j+b], imulS(ac_k, imulS(P_iv[j][a], P_iv[i][b])))
                    # (3j+a, 3i+b): ac_k * P_ia * P_jb
                    H_iv[3*j+a][3*i+b] = iadd(H_iv[3*j+a][3*i+b], imulS(ac_k, imulS(P_iv[i][a], P_iv[j][b])))
    # 3) Normal penalty K_norm = 10: 10 * P_ia * P_ib on (3i+a, 3i+b)
    for i in range(9):
        for a in range(3):
            for b in range(3):
                H_iv[3*i+a][3*i+b] = iadd(H_iv[3*i+a][3*i+b], iscale(10, imulS(P_iv[i][a], P_iv[i][b])))
    # 4) Rot penalty K_rot = 5: for (a,b) in {(0,1),(0,2),(1,2)}, v[3i+b]=P_ia, v[3i+a]=-P_ib
    for (a, b) in [(0, 1), (0, 2), (1, 2)]:
        v = [(0, 0)] * 27
        for i in range(9):
            v[3*i+b] = P_iv[i][a]
            v[3*i+a] = ineg(P_iv[i][b])
        for p in range(27):
            if v[p] == (0, 0): continue
            for q in range(27):
                if v[q] == (0, 0): continue
                H_iv[p][q] = iadd(H_iv[p][q], iscale(5, imulS(v[p], v[q])))

    # Symmetrize H_rat = midpoint of H_iv (integer at scale S = 10^6)
    H_rat = [[0]*27 for _ in range(27)]
    max_rad = 0
    for p in range(27):
        for q in range(27):
            mid = (H_iv[p][q][0] + H_iv[p][q][1] + H_iv[q][p][0] + H_iv[q][p][1]) // 4
            H_rat[p][q] = mid
            rad = max(abs(H_iv[p][q][0] - mid), abs(H_iv[p][q][1] - mid))
            max_rad = max(max_rad, rad)
    print(f"[OK] H_iv max radius around H_rat = {max_rad} / 10^6 = {max_rad/S:.2e}")
    assert max_rad <= 50, f"max_rad {max_rad} > 50!"

    # Compute high-precision Cholesky of M = H_rat/S - (1/25)*I_27 = C * C^T
    # Store C_int = round(C * S) (scale S = 10^6), so C_int * C_int^T approximates S * (H_rat - 40000*I_27)
    A = mp.matrix([[mp.mpf(H_rat[p][q] - (40000 if p == q else 0)) / S for q in range(27)] for p in range(27)])
    L = mp.cholesky(A)
    C_int = [[int(mp.nint(L[p, q] * S)) if q <= p else 0 for q in range(27)] for p in range(27)]
    max_chol_err = 0
    for p in range(27):
        for q in range(27):
            dot = sum(C_int[p][k] * C_int[q][k] for k in range(27))
            target = S * (H_rat[p][q] - (40000 if p == q else 0))
            max_chol_err = max(max_chol_err, abs(target - dot))
    print(f"[OK] Cholesky max entry err = {max_chol_err} / 10^12 = {max_chol_err/(S*S):.2e}")
    assert max_chol_err <= 10**7  # <= 1e-5 in R!

    # Check total guaranteed quadratic lower bound:
    # H_true >= 1/25 - 27*(50/10^6 + 10^7/10^12) = 0.04 - 27*(0.00006) = 0.03838
    # Minus err_norm(0.00001) + err_q(0.0016) = 0.03677 > 1/30 = 0.03333!
    margin_total = 0.04 - 27 * (50/1e6 + 1e-5) - 0.00001 - 0.0016
    print(f"[OK] Certified strict quadratic lower bound >= {margin_total:.5f} > 1/30 = 0.03333!")
    assert margin_total > 1/30

    def q_lit(f: Fraction) -> str:
        return f"({f.numerator} : ℚ) / {f.denominator}"

    def fmt_mat(M):
        rows = ["  #[" + ", ".join(str(x) for x in row) + "]" for row in M]
        return "#[\n" + ",\n".join(rows) + "\n]"

    lines = [
        "import ThomsonN9.TableB1",
        "import ThomsonN9.TableB5Data",
        "",
        "/-!",
        "# Thomson N = 9 Stage B — L6 Local Minimality Data & 27×27 Hessian Certificate",
        "",
        "Auto-generated by `numerics/bounds/export_lean_l6.py`.",
        "-/",
        "",
        "set_option maxHeartbeats 8000000",
        "set_option maxRecDepth 200000",
        "",
        "namespace ThomsonN9.StageB.LocalMinL6Data",
        "",
        "open ThomsonN9.TableB1 ThomsonN9.TableB5Data",
        "",
        f"def zStarLo : ℚ := {Z_LO.numerator} / {Z_LO.denominator}",
        f"def zStarHi : ℚ := {Z_HI.numerator} / {Z_HI.denominator}",
        f"def E_ttp_hi_q : ℚ := {E_TTP_HI_NUM} / {E_TTP_HI_DEN}",
        "",
        "theorem zStar_in_zBox : zLo ≤ zStarLo ∧ zStarLo < zStarHi ∧ zStarHi ≤ zHi := by",
        "  refine ⟨?_, ?_, ?_⟩ <;> norm_num [zLo, zHi, zStarLo, zStarHi]",
        "",
        "/-! ## Tight 20-Digit Square-Root Envelopes on `[zStarLo, zStarHi]` -/",
        f"def s3Lo : ℚ := {s3_lo.numerator} / {s3_lo.denominator}",
        f"def s3Hi : ℚ := {s3_hi.numerator} / {s3_hi.denominator}",
        f"def rhoStarLo : ℚ := {rho_lo.numerator} / {rho_lo.denominator}",
        f"def rhoStarHi : ℚ := {rho_hi.numerator} / {rho_hi.denominator}",
        f"def r0Lo : ℚ := {r0_lo.numerator} / {r0_lo.denominator}",
        f"def r0Hi : ℚ := {r0_hi.numerator} / {r0_hi.denominator}",
        f"def r1Lo : ℚ := {r1_lo.numerator} / {r1_lo.denominator}",
        f"def r1Hi : ℚ := {r1_hi.numerator} / {r1_hi.denominator}",
        f"def r5Lo : ℚ := {r5_lo.numerator} / {r5_lo.denominator}",
        f"def r5Hi : ℚ := {r5_hi.numerator} / {r5_hi.denominator}",
        "",
        "theorem env_sq_ok :",
        "    s3Lo ^ 2 ≤ 3 ∧ 3 ≤ s3Hi ^ 2 ∧ 0 < s3Lo ∧",
        "    rhoStarLo ^ 2 ≤ 1 - zStarHi ^ 2 ∧ 1 - zStarLo ^ 2 ≤ rhoStarHi ^ 2 ∧ 0 < rhoStarLo ∧",
        "    r0Lo ^ 2 ≤ 3 + zStarLo ^ 2 ∧ 3 + zStarHi ^ 2 ≤ r0Hi ^ 2 ∧ 0 < r0Lo ∧",
        "    r1Lo ^ 2 ≤ 2 + 2 * rhoStarLo ∧ 2 + 2 * rhoStarHi ≤ r1Hi ^ 2 ∧ 0 < r1Lo ∧",
        "    r5Lo ^ 2 ≤ 2 - rhoStarHi ∧ 2 - rhoStarLo ≤ r5Hi ^ 2 ∧ 0 < r5Lo := by",
        "  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>",
        "    norm_num [s3Lo, s3Hi, rhoStarLo, rhoStarHi, r0Lo, r0Hi, r1Lo, r1Hi, r5Lo, r5Hi, zStarLo, zStarHi]",
        "",
        "theorem E_hi_env_ok :",
        "    2 * s3Hi / rhoStarLo + s3Hi + 3 / (2 * zStarLo) + 6 / r0Lo + 12 / r5Lo + 6 / r1Lo ≤ E_ttp_hi_q := by",
        "  norm_num [s3Hi, rhoStarLo, zStarLo, r0Lo, r5Lo, r1Lo, E_ttp_hi_q]",
        "",
        "/-! ## Pointwise Criticality Sign-Change Envelopes at `zStarLo` and `zStarHi` -/",
        f"def cLo_s3l : ℚ := {cLo['s3l'].numerator} / {cLo['s3l'].denominator}",
        f"def cLo_s3h : ℚ := {cLo['s3h'].numerator} / {cLo['s3h'].denominator}",
        f"def cLo_rl  : ℚ := {cLo['rl'].numerator} / {cLo['rl'].denominator}",
        f"def cLo_rh  : ℚ := {cLo['rh'].numerator} / {cLo['rh'].denominator}",
        f"def cLo_a0h : ℚ := {cLo['a0h'].numerator} / {cLo['a0h'].denominator}",
        f"def cLo_a1l : ℚ := {cLo['a1l'].numerator} / {cLo['a1l'].denominator}",
        f"def cLo_a5h : ℚ := {cLo['a5h'].numerator} / {cLo['a5h'].denominator}",
        "",
        f"def cHi_s3h : ℚ := {cHi['s3h'].numerator} / {cHi['s3h'].denominator}",
        f"def cHi_rl  : ℚ := {cHi['rl'].numerator} / {cHi['rl'].denominator}",
        f"def cHi_rh  : ℚ := {cHi['rh'].numerator} / {cHi['rh'].denominator}",
        f"def cHi_a0l : ℚ := {cHi['a0l'].numerator} / {cHi['a0l'].denominator}",
        f"def cHi_a1h : ℚ := {cHi['a1h'].numerator} / {cHi['a1h'].denominator}",
        f"def cHi_a5l : ℚ := {cHi['a5l'].numerator} / {cHi['a5l'].denominator}",
        "",
        "theorem critLo_sq_ok :",
        "    cLo_s3l ^ 2 ≤ 3 ∧ 0 < cLo_s3l ∧",
        "    cLo_rl ^ 2 ≤ 1 - zStarLo ^ 2 ∧ 1 - zStarLo ^ 2 ≤ cLo_rh ^ 2 ∧ 0 < cLo_rl ∧",
        "    3 + zStarLo ^ 2 ≤ cLo_a0h ^ 2 ∧ 0 < cLo_a0h ∧",
        "    cLo_a1l ^ 2 ≤ 2 + 2 * cLo_rl ∧ 0 < cLo_a1l ∧",
        "    2 - cLo_rl ≤ cLo_a5h ^ 2 ∧ 0 < cLo_a5h := by",
        "  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>",
        "    norm_num [cLo_s3l, cLo_rl, cLo_rh, cLo_a0h, cLo_a1l, cLo_a5h, zStarLo]",
        "",
        "theorem critLo_neg_ok :",
        "    3 / (cLo_s3l * cLo_rl) ^ 3 - 2 / (2 * zStarLo) ^ 3 - 1 / cLo_a0h ^ 3",
        "      - 1 / (cLo_a5h ^ 3 * cLo_rh) + 1 / (cLo_a1l ^ 3 * cLo_rl) < 0 := by",
        "  norm_num [cLo_s3l, cLo_rl, cLo_rh, cLo_a0h, cLo_a1l, cLo_a5h, zStarLo]",
        "",
        "theorem critHi_sq_ok :",
        "    3 ≤ cHi_s3h ^ 2 ∧ 0 < cHi_s3h ∧",
        "    cHi_rl ^ 2 ≤ 1 - zStarHi ^ 2 ∧ 1 - zStarHi ^ 2 ≤ cHi_rh ^ 2 ∧ 0 < cHi_rl ∧",
        "    cHi_a0l ^ 2 ≤ 3 + zStarHi ^ 2 ∧ 0 < cHi_a0l ∧",
        "    2 + 2 * cHi_rh ≤ cHi_a1h ^ 2 ∧ 0 < cHi_a1h ∧",
        "    cHi_a5l ^ 2 ≤ 2 - cHi_rh ∧ 0 < cHi_a5l := by",
        "  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>",
        "    norm_num [cHi_s3h, cHi_rl, cHi_rh, cHi_a0l, cHi_a1h, cHi_a5l, zStarHi]",
        "",
        "theorem critHi_pos_ok :",
        "    0 < 3 / (cHi_s3h * cHi_rh) ^ 3 - 2 / (2 * zStarHi) ^ 3 - 1 / cHi_a0l ^ 3",
        "      - 1 / (cHi_a5l ^ 3 * cHi_rl) + 1 / (cHi_a1h ^ 3 * cHi_rh) := by",
        "  norm_num [cHi_s3h, cHi_rl, cHi_rh, cHi_a0l, cHi_a1h, cHi_a5l, zStarHi]",
        "",
        "/-! ## Shifted Bregman Root Envelopes (`√(2 - 2*(ν_k - 1/200))`) -/",
    ]
    for k, (sr_lo, sr_hi) in enumerate(q_shift_box):
        lines.append(f"def srLo_{k} : ℚ := {sr_lo.numerator} / {sr_lo.denominator}")
        lines.append(f"def srHi_{k} : ℚ := {sr_hi.numerator} / {sr_hi.denominator}")
    lines += [
        "",
        "theorem sr_sq_ok :",
        "    srLo_0 ^ 2 ≤ 3 + zStarLo ^ 2 + 1 / 100 ∧ 3 + zStarHi ^ 2 + 1 / 100 ≤ srHi_0 ^ 2 ∧ 0 < srLo_0 ∧",
        "    srLo_1 ^ 2 ≤ 2 + 2 * rhoStarLo + 1 / 100 ∧ 2 + 2 * rhoStarHi + 1 / 100 ≤ srHi_1 ^ 2 ∧ 0 < srLo_1 ∧",
        "    srLo_2 ^ 2 ≤ 3 + 1 / 100 ∧ 3 + 1 / 100 ≤ srHi_2 ^ 2 ∧ 0 < srLo_2 ∧",
        "    srLo_3 ^ 2 ≤ 4 * zStarLo ^ 2 + 1 / 100 ∧ 4 * zStarHi ^ 2 + 1 / 100 ≤ srHi_3 ^ 2 ∧ 0 < srLo_3 ∧",
        "    srLo_4 ^ 2 ≤ 3 * (1 - zStarHi ^ 2) + 1 / 100 ∧ 3 * (1 - zStarLo ^ 2) + 1 / 100 ≤ srHi_4 ^ 2 ∧ 0 < srLo_4 ∧",
        "    srLo_5 ^ 2 ≤ 2 - rhoStarHi + 1 / 100 ∧ 2 - rhoStarLo + 1 / 100 ≤ srHi_5 ^ 2 ∧ 0 < srLo_5 := by",
        "  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>",
        "    norm_num [srLo_0, srHi_0, srLo_1, srHi_1, srLo_2, srHi_2, srLo_3, srHi_3, srLo_4, srHi_4, srLo_5, srHi_5,",
        "      zStarLo, zStarHi, rhoStarLo, rhoStarHi]",
        "",
        "theorem c5_le_one_ok :",
        "    (3 : ℚ) / (2 * srLo_0 ^ 5) ≤ 1 ∧ (3 : ℚ) / (2 * srLo_1 ^ 5) ≤ 1 ∧",
        "    (3 : ℚ) / (2 * srLo_2 ^ 5) ≤ 1 ∧ (3 : ℚ) / (2 * srLo_3 ^ 5) ≤ 1 ∧",
        "    (3 : ℚ) / (2 * srLo_4 ^ 5) ≤ 1 ∧ (3 : ℚ) / (2 * srLo_5 ^ 5) ≤ 1 := by",
        "  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [srLo_0, srLo_1, srLo_2, srLo_3, srLo_4, srLo_5]",
        "",
        "/-! ## Scale-`10^6` Interval Arithmetic & 27×27 Penalized Hessian Certificate -/",
        "",
        "structure Iv6 where",
        "  lo : ℤ",
        "  hi : ℤ",
        "",
        "def S6 : ℤ := 1000000",
        "def i6Add (x y : Iv6) : Iv6 := ⟨x.lo + y.lo, x.hi + y.hi⟩",
        "def i6Sub (x y : Iv6) : Iv6 := ⟨x.lo - y.hi, x.hi - y.lo⟩",
        "def i6Neg (x : Iv6) : Iv6 := ⟨-x.hi, -x.lo⟩",
        "def i6Div2 (x : Iv6) : Iv6 := ⟨Int.ediv x.lo 2, Int.ediv (x.hi + 1) 2⟩",
        "def i6Scale (k : ℤ) (x : Iv6) : Iv6 :=",
        "  if 0 ≤ k then ⟨k * x.lo, k * x.hi⟩ else ⟨k * x.hi, k * x.lo⟩",
        "def i6Mul (x y : Iv6) : Iv6 :=",
        "  let p1 := x.lo * y.lo; let p2 := x.lo * y.hi",
        "  let p3 := x.hi * y.lo; let p4 := x.hi * y.hi",
        "  let lo := min (min p1 p2) (min p3 p4)",
        "  let hi := max (max p1 p2) (max p3 p4)",
        "  ⟨Int.ediv lo S6, -Int.ediv (-hi) S6⟩",
        "",
        f"def ivZ : Iv6 := ⟨{iv_z[0]}, {iv_z[1]}⟩",
        f"def ivRho : Iv6 := ⟨{iv_rho[0]}, {iv_rho[1]}⟩",
        f"def ivS3 : Iv6 := ⟨{iv_s3[0]}, {iv_s3[1]}⟩",
        f"def ivS3Rho : Iv6 := ⟨{iv_s3rho[0]}, {iv_s3rho[1]}⟩",
        f"def ivLamP : Iv6 := ⟨{iv_lamP[0]}, {iv_lamP[1]}⟩",
        f"def ivLamC : Iv6 := ⟨{iv_lamC[0]}, {iv_lamC[1]}⟩",
        "",
        "def ivPhi3 : ℕ → Iv6",
    ]
    for k, (a, b) in enumerate(iv_phi3):
        pat = "_" if k == 5 else str(k)
        lines.append(f"  | {pat} => ⟨{a}, {b}⟩")
    lines += [
        "",
        "def ivAC5 : ℕ → Iv6",
    ]
    for k, (a, b) in enumerate(iv_ac5):
        pat = "_" if k == 5 else str(k)
        lines.append(f"  | {pat} => ⟨{a}, {b}⟩")
    lines += [
        "",
        "def ivP (i a : ℕ) : Iv6 :=",
        "  match i, a with",
        "  | 0, 0 => ivRho | 0, 1 => ⟨0, 0⟩ | 0, 2 => ivZ",
        "  | 1, 0 => i6Neg (i6Div2 ivRho) | 1, 1 => i6Div2 ivS3Rho | 1, 2 => ivZ",
        "  | 2, 0 => i6Neg (i6Div2 ivRho) | 2, 1 => i6Neg (i6Div2 ivS3Rho) | 2, 2 => ivZ",
        "  | 3, 0 => ivRho | 3, 1 => ⟨0, 0⟩ | 3, 2 => i6Neg ivZ",
        "  | 4, 0 => i6Neg (i6Div2 ivRho) | 4, 1 => i6Div2 ivS3Rho | 4, 2 => i6Neg ivZ",
        "  | 5, 0 => i6Neg (i6Div2 ivRho) | 5, 1 => i6Neg (i6Div2 ivS3Rho) | 5, 2 => i6Neg ivZ",
        "  | 6, 0 => ⟨500000, 500000⟩ | 6, 1 => i6Div2 ivS3 | 6, 2 => ⟨0, 0⟩",
        "  | 7, 0 => ⟨-1000000, -1000000⟩ | 7, 1 => ⟨0, 0⟩ | 7, 2 => ⟨0, 0⟩",
        "  | 8, 0 => ⟨500000, 500000⟩ | 8, 1 => i6Neg (i6Div2 ivS3) | 8, 2 => ⟨0, 0⟩",
        "  | _, _ => ⟨0, 0⟩",
        "",
        "def ivRotVec (a b p : ℕ) : Iv6 :=",
        "  let i := p / 3; let c := p % 3",
        "  if c == b then ivP i a else if c == a then i6Neg (ivP i b) else ⟨0, 0⟩",
        "",
        "def ivHentry (p q : ℕ) : Iv6 :=",
        "  let i := p / 3; let a := p % 3",
        "  let j := q / 3; let b := q % 3",
        "  let diagLam : Iv6 := if p == q then i6Neg (i6Div2 (if i < 6 then ivLamP else ivLamC)) else ⟨0, 0⟩",
        "  let offPhi : Iv6 := if i != j && a == b then i6Div2 (ivPhi3 (nodeOfN i j)) else ⟨0, 0⟩",
        "  let bregDiag : Iv6 :=",
        "    if i == j then",
        "      (List.range 9).foldl (fun acc k =>",
        "        if k == i then acc",
        "        else i6Add acc (i6Mul (ivAC5 (nodeOfN i k)) (i6Mul (ivP k a) (ivP k b)))) ⟨0, 0⟩",
        "    else",
        "      i6Mul (ivAC5 (nodeOfN i j)) (i6Mul (ivP j a) (ivP i b))",
        "  let normPen : Iv6 := if i == j then i6Scale 10 (i6Mul (ivP i a) (ivP i b)) else ⟨0, 0⟩",
        "  let rot01 := i6Scale 5 (i6Mul (ivRotVec 0 1 p) (ivRotVec 0 1 q))",
        "  let rot02 := i6Scale 5 (i6Mul (ivRotVec 0 2 p) (ivRotVec 0 2 q))",
        "  let rot12 := i6Scale 5 (i6Mul (ivRotVec 1 2 p) (ivRotVec 1 2 q))",
        "  i6Add (i6Add (i6Add diagLam offPhi) (i6Add bregDiag normPen)) (i6Add (i6Add rot01 rot02) rot12)",
        "",
        f"def H_rat : Array (Array ℤ) := {fmt_mat(H_rat)}",
        "",
        f"def C_27 : Array (Array ℤ) := {fmt_mat(C_int)}",
        "",
        "def get27 (M : Array (Array ℤ)) (p q : ℕ) : ℤ := (M.getD p #[]).getD q 0",
        "",
        "def checkHIv : Bool :=",
        "  (List.range 27).all fun p =>",
        "    (List.range 27).all fun q =>",
        "      let iv := ivHentry p q",
        "      let r := get27 H_rat p q",
        "      decide (r - 50 ≤ iv.lo ∧ iv.hi ≤ r + 50)",
        "",
        "def checkHChol : Bool :=",
        "  (List.range 27).all fun p =>",
        "    (List.range 27).all fun q =>",
        "      let dot := (List.range 27).foldl (fun acc k => acc + get27 C_27 p k * get27 C_27 q k) 0",
        "      let target := S6 * (get27 H_rat p q - if p == q then 40000 else 0)",
        "      decide (target - 10000000 ≤ dot ∧ dot ≤ target + 10000000)",
        "",
        "theorem H_iv_ok : checkHIv = true := by decide +kernel",
        "theorem H_chol_ok : checkHChol = true := by decide +kernel",
        "",
        "/-! ## Rational Bridge Checks for the 15 Scalar `Iv6` Intervals -/",
        "theorem iv_scalars_ok :",
        "    (ivZ.lo : ℚ) / 1000000 ≤ zStarLo ∧ zStarHi ≤ (ivZ.hi : ℚ) / 1000000 ∧",
        "    (ivRho.lo : ℚ) / 1000000 ≤ rhoStarLo ∧ rhoStarHi ≤ (ivRho.hi : ℚ) / 1000000 ∧",
        "    (ivS3.lo : ℚ) / 1000000 ≤ s3Lo ∧ s3Hi ≤ (ivS3.hi : ℚ) / 1000000 ∧",
        "    (ivS3Rho.lo : ℚ) / 1000000 ≤ s3Lo * rhoStarLo ∧ s3Hi * rhoStarHi ≤ (ivS3Rho.hi : ℚ) / 1000000 ∧",
        "    ((ivPhi3 0).lo : ℚ) / 1000000 ≤ 1 / r0Hi ^ 3 ∧ 1 / r0Lo ^ 3 ≤ ((ivPhi3 0).hi : ℚ) / 1000000 ∧",
        "    ((ivPhi3 1).lo : ℚ) / 1000000 ≤ 1 / r1Hi ^ 3 ∧ 1 / r1Lo ^ 3 ≤ ((ivPhi3 1).hi : ℚ) / 1000000 ∧",
        "    ((ivPhi3 2).lo : ℚ) / 1000000 ≤ 1 / s3Hi ^ 3 ∧ 1 / s3Lo ^ 3 ≤ ((ivPhi3 2).hi : ℚ) / 1000000 ∧",
        "    ((ivPhi3 3).lo : ℚ) / 1000000 ≤ 1 / (2 * zStarHi) ^ 3 ∧ 1 / (2 * zStarLo) ^ 3 ≤ ((ivPhi3 3).hi : ℚ) / 1000000 ∧",
        "    ((ivPhi3 4).lo : ℚ) / 1000000 ≤ 1 / (s3Hi * rhoStarHi) ^ 3 ∧ 1 / (s3Lo * rhoStarLo) ^ 3 ≤ ((ivPhi3 4).hi : ℚ) / 1000000 ∧",
        "    ((ivPhi3 5).lo : ℚ) / 1000000 ≤ 1 / r5Hi ^ 3 ∧ 1 / r5Lo ^ 3 ≤ ((ivPhi3 5).hi : ℚ) / 1000000 ∧",
        "    ((ivAC5 0).lo : ℚ) / 1000000 ≤ 99 / 100 * (3 / (2 * srHi_0 ^ 5)) ∧ 99 / 100 * (3 / (2 * srLo_0 ^ 5)) ≤ ((ivAC5 0).hi : ℚ) / 1000000 ∧",
        "    ((ivAC5 1).lo : ℚ) / 1000000 ≤ 99 / 100 * (3 / (2 * srHi_1 ^ 5)) ∧ 99 / 100 * (3 / (2 * srLo_1 ^ 5)) ≤ ((ivAC5 1).hi : ℚ) / 1000000 ∧",
        "    ((ivAC5 2).lo : ℚ) / 1000000 ≤ 99 / 100 * (3 / (2 * srHi_2 ^ 5)) ∧ 99 / 100 * (3 / (2 * srLo_2 ^ 5)) ≤ ((ivAC5 2).hi : ℚ) / 1000000 ∧",
        "    ((ivAC5 3).lo : ℚ) / 1000000 ≤ 99 / 100 * (3 / (2 * srHi_3 ^ 5)) ∧ 99 / 100 * (3 / (2 * srLo_3 ^ 5)) ≤ ((ivAC5 3).hi : ℚ) / 1000000 ∧",
        "    ((ivAC5 4).lo : ℚ) / 1000000 ≤ 99 / 100 * (3 / (2 * srHi_4 ^ 5)) ∧ 99 / 100 * (3 / (2 * srLo_4 ^ 5)) ≤ ((ivAC5 4).hi : ℚ) / 1000000 ∧",
        "    ((ivAC5 5).lo : ℚ) / 1000000 ≤ 99 / 100 * (3 / (2 * srHi_5 ^ 5)) ∧ 99 / 100 * (3 / (2 * srLo_5 ^ 5)) ≤ ((ivAC5 5).hi : ℚ) / 1000000 ∧",
        "    (ivLamP.lo : ℚ) / 1000000 ≤ 2 / (s3Hi * rhoStarHi) ^ 3 - 1 / (2 * zStarLo) ^ 3 - 2 / r0Lo ^ 3 ∧",
        "    2 / (s3Lo * rhoStarLo) ^ 3 - 1 / (2 * zStarHi) ^ 3 - 2 / r0Hi ^ 3 ≤ (ivLamP.hi : ℚ) / 1000000 ∧",
        "    (ivLamC.lo : ℚ) / 1000000 ≤ 2 * rhoStarLo / r5Hi ^ 3 - 2 * rhoStarHi / r1Lo ^ 3 - 1 / s3Lo ^ 3 ∧",
        "    2 * rhoStarHi / r5Lo ^ 3 - 2 * rhoStarLo / r1Hi ^ 3 - 1 / s3Hi ^ 3 ≤ (ivLamC.hi : ℚ) / 1000000 := by",
        "  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,",
        "          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>",
        "    norm_num [ivZ, ivRho, ivS3, ivS3Rho, ivPhi3, ivAC5, ivLamP, ivLamC,",
        "      zStarLo, zStarHi, rhoStarLo, rhoStarHi, s3Lo, s3Hi, r0Lo, r0Hi, r1Lo, r1Hi, r5Lo, r5Hi,",
        "      srLo_0, srHi_0, srLo_1, srHi_1, srLo_2, srHi_2, srLo_3, srHi_3, srLo_4, srHi_4, srLo_5, srHi_5]",
        "",
        "end ThomsonN9.StageB.LocalMinL6Data",
        "",
    ]
    OUT.write_text("\n".join(lines))
    print(f"Wrote {OUT} ({OUT.stat().st_size / 1024:.1f} KB)")


if __name__ == "__main__":
    main()
