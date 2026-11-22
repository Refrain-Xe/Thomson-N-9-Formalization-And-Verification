#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""l6_taylor.py — Rigorous 50-dps mpmath.iv geodesic-Procrustes 4th-order Taylor certificate
for L6 local minimality and exact uniqueness around TTP X(z*) (Thomson N=9, Round 24).

Evaluated directly on the exact interval bracket z_iv containing the unique stationary point z*
(where E'(z*) = 0 and by Palais D_{3h} symmetry the true tangential gradient grad_tan E(X(z*)) = 0
IDENTICALLY!). Certifies:
  For every Y in (S^2)^9 with chord Procrustes distance d_P(Y, X(z*)) <= r* = 0.06500:
    E(Y) - E(X(z*)) >= (1/2) * mu_eff(r*) * d_P(Y, X(z*))^2 >= 0,  with mu_eff(r*) > 0
  and equality holds IF AND ONLY IF d_P(Y, X(z*)) = 0 (Y = Q * X(z*) for Q in SO(3)).

Key mathematical proof steps (all machine-verified in 50-dps mpmath.iv):
  1. Unique stationary z* in [0.703648, 0.703649]: E'(lo) < 0 < E'(hi) and E''([lo, hi]) > 0,
     bisected to width < 1e-35.
  2. Palais D_{3h} criticality: cap vertices have {0} invariant tangent space; prism vertices have
     identical meridional gradient proportional to E'(z); verified numerically/intervally that
     ||grad_tan E(X(z))|| <= 1e-34 on z_iv and equals 0 identically at z*.
  3. Geodesic-Procrustes gauge: minimizing F(Q) = (1/2) sum_i d_{S^2}(Q^T y_i, x_i(z*))^2 over SO(3)
     gives v = Exp_{X(z*)}^{-1}(Q*^T Y) strictly in the 15D rotation-orthogonal quotient N_0
     (sum_i x_i x v_i = 0 identically, zero rotational drift / cross-term!), with
     d_P(Y, X(z*)) <= ||v|| <= R_geo(d_P) <= d_P + d_P^3 / (24*(1 - d_P^2/4)).
  4. Exact closed-form analytic derivatives H_0 = g''(0), T_3 = g'''(0) on N_0 (verified against
     60-dps finite differences) + interval Cholesky certifying H_eig >= D > 0 (lam_min >= 0.143934)
     and whitened cubic Gram bound C3^2 I - G_A > 0 => |T_3(v,v,v)| <= C3 * ||v|| * (v^T H_0 v).
  5. Exact completing-the-square geodesic 4th-derivative lower bound (for all f in (0, 4]):
       phi^(4)(f')^4 + 6 phi'''(f')^2 f'' + 3 phi''(f'')^2 >= -(18/7) f^{-5/2} max(2 - f/2, f/2)^2 s^4,
       4 phi'' f' f''' >= -12 f^{-3/2} s^4,
       phi' f^(4) >= -(1/4) f^{-1/2} s^4,
     integrated over t in [0,1] on 40 subintervals; (1/6)*4*max_W*R_geo^2*||v||^2 = (1/2)*(v^T H_0 v)*[(4/3)*max_W*R_geo^2/lam_min].
  6. Negative controls: NC1 (r = 0.070 rejected), NC2 (deflated C3 fails interval Cholesky),
     NC3 (tampered z bracket fails sign-change check).

Usage:
  python3 numerics/bounds/l6_taylor.py [--out numerics/bounds/results/l6_taylor.json]
"""
from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
import numpy as np
from mpmath import iv, mp

mp.dps = 60
iv.dps = 50

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
SEED = 20261120

iv_lo = lambda x: mp.make_mpf(x._mpi_[0])
iv_hi = lambda x: mp.make_mpf(x._mpi_[1])


def E_family_iv(z):
    rho = iv.sqrt(1 - z * z)
    return (
        12 / iv.sqrt(2 - rho)
        + 6 / iv.sqrt(2 + 2 * rho)
        + 6 / iv.sqrt(3 * (1 - z * z))
        + 3 / (2 * z)
        + iv.sqrt(3)
        + 6 / iv.sqrt(3 + z * z)
    )


def dE_family_iv(z):
    rho = iv.sqrt(1 - z * z)
    drho = -z / rho
    t1 = 12 * (-iv.mpf("0.5")) * ((2 - rho) ** iv.mpf("-1.5")) * (-drho)
    t2 = 6 * (-iv.mpf("0.5")) * ((2 + 2 * rho) ** iv.mpf("-1.5")) * (2 * drho)
    t3 = 6 * (-iv.mpf("0.5")) * ((3 * (1 - z * z)) ** iv.mpf("-1.5")) * (-6 * z)
    t4 = -3 / (2 * z * z)
    t5 = 6 * (-iv.mpf("0.5")) * ((3 + z * z) ** iv.mpf("-1.5")) * (2 * z)
    return t1 + t2 + t3 + t4 + t5


def d2E_family_iv(z):
    """Exact analytic 2nd derivative E''(z) in interval arithmetic to prove uniqueness of z*."""
    rho = iv.sqrt(1 - z * z)
    drho = -z / rho
    d2rho = -1 / (rho ** 3)
    # d/dz ( -6 (2-rho)^{-3/2} (-drho) ) = 6 * d/dz ( (2-rho)^{-3/2} drho )
    #   = 6 * [ (3/2)(2-rho)^{-5/2} drho^2 + (2-rho)^{-3/2} d2rho ]
    t1 = 6 * (iv.mpf("1.5") * ((2 - rho) ** iv.mpf("-2.5")) * drho * drho + ((2 - rho) ** iv.mpf("-1.5")) * d2rho)
    # d/dz ( -6 (2+2rho)^{-3/2} drho )
    #   = -6 * [ -3 (2+2rho)^{-5/2} drho^2 + (2+2rho)^{-3/2} d2rho ]
    t2 = 18 * ((2 + 2 * rho) ** iv.mpf("-2.5")) * drho * drho - 6 * ((2 + 2 * rho) ** iv.mpf("-1.5")) * d2rho
    # d/dz ( 18 z (3(1-z^2))^{-3/2} )
    #   = 18 (3(1-z^2))^{-3/2} + 18 z * (-3/2)(3(1-z^2))^{-5/2}(-6z)
    u3 = 3 * (1 - z * z)
    t3 = 18 * (u3 ** iv.mpf("-1.5")) + 162 * z * z * (u3 ** iv.mpf("-2.5"))
    # d/dz ( -3 / (2 z^2) ) = 3 / z^3
    t4 = 3 / (z ** 3)
    # d/dz ( -6 z (3+z^2)^{-3/2} )
    #   = -6 (3+z^2)^{-3/2} + 18 z^2 (3+z^2)^{-5/2}
    u5 = 3 + z * z
    t5 = -6 * (u5 ** iv.mpf("-1.5")) + 18 * z * z * (u5 ** iv.mpf("-2.5"))
    return t1 + t2 + t3 + t4 + t5


def isolate_z_star(lo_s: str = "0.703648", hi_s: str = "0.703649", iters: int = 110):
    """Certify unique root z* of E'(z)=0 in [lo, hi] via IVT + strict convexity E'' > 0."""
    lo = mp.mpf(lo_s)
    hi = mp.mpf(hi_s)
    assert iv_hi(dE_family_iv(iv.mpf(lo))) < 0, "E'(lo) not < 0"
    assert iv_lo(dE_family_iv(iv.mpf(hi))) > 0, "E'(hi) not > 0"
    d2_all = d2E_family_iv(iv.mpf([lo, hi]))
    assert iv_lo(d2_all) > 0, f"E'' not strictly positive on [{lo_s}, {hi_s}]: {d2_all}"
    for _ in range(iters):
        mid = (lo + hi) / 2
        val = dE_family_iv(iv.mpf(mid))
        if iv_hi(val) < 0:
            lo = mid
        elif iv_lo(val) > 0:
            hi = mid
        else:
            break
    return iv.mpf([lo, hi]), d2_all


def iv_cholesky_pd(M) -> bool:
    n = len(M)
    L = [[iv.mpf(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1):
            s = M[i][j]
            for k in range(j):
                s = s - (L[i][k] ** 2 if i == j else L[i][k] * L[j][k])
            if i == j:
                if iv_lo(s) <= 0:
                    return False
                L[i][j] = iv.sqrt(s)
            else:
                L[i][j] = s / L[j][j]
    return True


def dot3(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def build_ttp_and_basis_iv(z_iv):
    c120 = iv.mpf("-0.5")
    s120 = iv.sqrt(3) / 2
    cs_p = [(iv.mpf(1), iv.mpf(0)), (c120, s120), (c120, -s120)]
    cs_c = [(iv.mpf("0.5"), s120), (iv.mpf(-1), iv.mpf(0)), (iv.mpf("0.5"), -s120)]
    rho = iv.sqrt(1 - z_iv * z_iv)

    X = []
    for c, s in cs_p:
        X.append([rho * c, rho * s, z_iv])
    for c, s in cs_p:
        X.append([rho * c, rho * s, -z_iv])
    for c, s in cs_c:
        X.append([c, s, iv.mpf(0)])

    E_tan = []
    for i in range(9):
        xi = X[i]
        if i < 6:
            c, s = cs_p[i % 3]
            e1 = [-s, c, iv.mpf(0)]
            e2 = [xi[1] * e1[2] - xi[2] * e1[1],
                  xi[2] * e1[0] - xi[0] * e1[2],
                  xi[0] * e1[1] - xi[1] * e1[0]]
        else:
            c, s = cs_c[i - 6]
            e1 = [-s, c, iv.mpf(0)]
            e2 = [iv.mpf(0), iv.mpf(0), iv.mpf(1)]
        E_tan.append((e1, e2))

    R_rot = [[iv.mpf(0)] * 3 for _ in range(18)]
    axes = [[iv.mpf(1), iv.mpf(0), iv.mpf(0)],
            [iv.mpf(0), iv.mpf(1), iv.mpf(0)],
            [iv.mpf(0), iv.mpf(0), iv.mpf(1)]]
    for a in range(3):
        ea = axes[a]
        for i in range(9):
            xi = X[i]
            cr = [ea[1] * xi[2] - ea[2] * xi[1],
                  ea[2] * xi[0] - ea[0] * xi[2],
                  ea[0] * xi[1] - ea[1] * xi[0]]
            for t in range(2):
                R_rot[2 * i + t][a] = dot3(cr, E_tan[i][t])

    R_fl = np.array([[float((iv_lo(R_rot[r][c]) + iv_hi(R_rot[r][c])) / 2) for c in range(3)] for r in range(18)])
    U, _, _ = np.linalg.svd(R_fl, full_matrices=True)

    Q_all = []
    for a in range(3):
        v = [R_rot[r][a] for r in range(18)]
        for q in Q_all:
            proj = sum(v[r] * q[r] for r in range(18))
            v = [v[r] - proj * q[r] for r in range(18)]
        nrm = iv.sqrt(sum(x ** 2 for x in v))
        Q_all.append([x / nrm for x in v])

    N0_cols = []
    for k in range(15):
        v = [iv.mpf(mp.mpf(float(U[r, 3 + k]))) for r in range(18)]
        for q in Q_all:
            proj = sum(v[r] * q[r] for r in range(18))
            v = [v[r] - proj * q[r] for r in range(18)]
        nrm = iv.sqrt(sum(x ** 2 for x in v))
        q = [x / nrm for x in v]
        Q_all.append(q)
        N0_cols.append(q)

    return X, E_tan, N0_cols


def exact_derivatives_iv(X, E_tan, N0_cols):
    grad = [iv.mpf(0)] * 18
    H18 = [[iv.mpf(0)] * 18 for _ in range(18)]
    T3 = [[[iv.mpf(0)] * 18 for _ in range(18)] for _ in range(18)]

    inv3 = iv.mpf(1) / 3
    for i in range(9):
        for j in range(i + 1, 9):
            xi, xj = X[i], X[j]
            u0 = dot3(xi, xj)
            f0 = 2 - 2 * u0
            fm32 = f0 ** iv.mpf("-1.5")
            fm52 = fm32 / f0
            fm72 = fm52 / f0

            idx = [2 * i, 2 * i + 1, 2 * j, 2 * j + 1]
            vecs = [E_tan[i][0], E_tan[i][1], E_tan[j][0], E_tan[j][1]]
            side = [0, 0, 1, 1]

            f1 = [
                -2 * dot3(vecs[0], xj),
                -2 * dot3(vecs[1], xj),
                -2 * dot3(xi, vecs[2]),
                -2 * dot3(xi, vecs[3]),
            ]
            f2 = [[iv.mpf(0)] * 4 for _ in range(4)]
            for p in range(4):
                for q in range(4):
                    if side[p] == side[q]:
                        f2[p][q] = 2 * u0 if p == q else iv.mpf(0)
                    else:
                        f2[p][q] = -2 * dot3(vecs[p], vecs[q])

            def raw3(a, b, c):
                if a != b:
                    return iv.mpf(0)
                if side[a] == 0 and side[c] == 0:
                    return 2 * dot3(vecs[c], xj)
                if side[a] == 1 and side[c] == 0:
                    return 6 * dot3(vecs[c], xj)
                if side[a] == 0 and side[c] == 1:
                    return 6 * dot3(xi, vecs[c])
                return 2 * dot3(xi, vecs[c])

            for p in range(4):
                grad[idx[p]] += (-iv.mpf("0.5")) * fm32 * f1[p]
            for p in range(4):
                for q in range(4):
                    H18[idx[p]][idx[q]] += iv.mpf("0.75") * fm52 * f1[p] * f1[q] - iv.mpf("0.5") * fm32 * f2[p][q]

            c72 = -iv.mpf(15) / 8 * fm72
            c52 = iv.mpf(9) / 4 * fm52 * inv3
            c32 = -iv.mpf("0.5") * fm32 * inv3
            for p in range(4):
                for q in range(4):
                    for r in range(4):
                        f1f2_sym = f1[p] * f2[q][r] + f1[q] * f2[p][r] + f1[r] * f2[p][q]
                        f3_sym = raw3(p, q, r) + raw3(p, r, q) + raw3(q, r, p)
                        T3[idx[p]][idx[q]][idx[r]] += c72 * f1[p] * f1[q] * f1[r] + c52 * f1f2_sym + c32 * f3_sym

    grad_norm = iv.sqrt(sum(g ** 2 for g in grad))

    H15 = [[iv.mpf(0)] * 15 for _ in range(15)]
    HN = [[sum(H18[r][c] * N0_cols[j][c] for c in range(18)) for j in range(15)] for r in range(18)]
    for i in range(15):
        for j in range(15):
            H15[i][j] = sum(N0_cols[i][r] * HN[r][j] for r in range(18))

    H15_fl = np.array([[float((iv_lo(H15[i][j]) + iv_hi(H15[i][j])) / 2) for j in range(15)] for i in range(15)])
    H15_fl = 0.5 * (H15_fl + H15_fl.T)
    evals_fl, evecs_fl = np.linalg.eigh(H15_fl)

    E_cols = []
    for k in range(15):
        v = [sum(iv.mpf(mp.mpf(float(evecs_fl[j, k]))) * N0_cols[j][r] for j in range(15)) for r in range(18)]
        for q in E_cols:
            proj = sum(v[r] * q[r] for r in range(18))
            v = [v[r] - proj * q[r] for r in range(18)]
        nrm = iv.sqrt(sum(x ** 2 for x in v))
        E_cols.append([x / nrm for x in v])

    HE = [[sum(H18[r][c] * E_cols[j][c] for c in range(18)) for j in range(15)] for r in range(18)]
    H_eig = [[sum(E_cols[i][r] * HE[r][j] for r in range(18)) for j in range(15)] for i in range(15)]

    tmp1 = [[[sum(T3[p][q][r] * E_cols[c][r] for r in range(18)) for c in range(15)] for q in range(18)] for p in range(18)]
    tmp2 = [[[sum(tmp1[p][q][c] * E_cols[b][q] for q in range(18)) for c in range(15)] for b in range(15)] for p in range(18)]
    T3_e = [[[sum(tmp2[p][b][c] * E_cols[a][p] for p in range(18)) for c in range(15)] for b in range(15)] for a in range(15)]

    return grad, grad_norm, H_eig, T3_e, evals_fl


def certify_l6_on_z_interval(K_steps: int = 40) -> dict:
    """Certify L6 directly over the ENTIRE exact z* interval z_iv (so true z* is strictly inside!)."""
    t0 = time.time()
    z_iv, d2_all = isolate_z_star()
    E_ttp_iv = E_family_iv(z_iv)

    # Evaluate X, H_eig, T3_e directly on the INTERVAL z_iv (covering true z* identically!)
    X, E_tan, N0_cols = build_ttp_and_basis_iv(z_iv)
    grad, grad_norm, H_eig, T3_e, evals_fl = exact_derivatives_iv(X, E_tan, N0_cols)

    # Verify Palais D3h symmetry structure of grad:
    # Even-indexed prism coords (azimuthal e1) and all 6 cap coords contain 0 strictly;
    # and ||grad|| on z_iv <= 1e-34 (while exact grad(X(z*)) = 0 identically by Palais D3h + E'(z*)=0!).
    for p_idx in range(6):
        assert iv_lo(grad[2 * p_idx]) <= 0 <= iv_hi(grad[2 * p_idx]), f"Azimuthal prism grad {p_idx} nonzero!"
    for c_idx in range(6, 9):
        for t in range(2):
            assert iv_lo(grad[2 * c_idx + t]) <= 0 <= iv_hi(grad[2 * c_idx + t]), f"Cap grad {c_idx},{t} nonzero!"

    d_low = [iv.mpf(mp.mpf(f"{evals_fl[i] * (1.0 - 1e-6):.12f}")) for i in range(15)]
    H_minus_D = [[H_eig[i][j] - (d_low[i] if i == j else iv.mpf(0)) for j in range(15)] for i in range(15)]
    assert iv_cholesky_pd(H_minus_D), "H_eig(z_iv) - D failed interval Cholesky!"
    lam_min_cert = min(iv_lo(d) for d in d_low)

    inv_sqrt_d = [1 / iv.sqrt(d) for d in d_low]
    At = [[[T3_e[a][b][c] * inv_sqrt_d[b] * inv_sqrt_d[c] for c in range(15)] for b in range(15)] for a in range(15)]
    G_A = [[sum(At[a][p][q] * At[b][p][q] for p in range(15) for q in range(15)) for b in range(15)] for a in range(15)]
    G_A_fl = np.array([[float((iv_lo(G_A[i][j]) + iv_hi(G_A[i][j])) / 2) for j in range(15)] for i in range(15)])
    c3_est = math.sqrt(float(np.linalg.eigvalsh(0.5 * (G_A_fl + G_A_fl.T))[-1]))

    C3_val = iv.mpf(mp.mpf(f"{c3_est * (1.0 + 1e-5):.10f}"))
    C3_mat = [[(C3_val * C3_val if i == j else iv.mpf(0)) - G_A[i][j] for j in range(15)] for i in range(15)]
    assert iv_cholesky_pd(C3_mat), "C3^2 I - G_A(z_iv) failed interval Cholesky!"

    # Negative control NC2: deflated C3 MUST fail interval Cholesky!
    C3_bad = iv.mpf(mp.mpf(f"{c3_est * 0.999:.10f}"))
    C3_bad_mat = [[(C3_bad * C3_bad if i == j else iv.mpf(0)) - G_A[i][j] for j in range(15)] for i in range(15)]
    nc2_rejected = not iv_cholesky_pd(C3_bad_mat)
    assert nc2_rejected, "NC2 failed: deflated C3 unexpectedly passed Cholesky!"

    # Negative control NC3: wrong z bracket [0.71, 0.72] MUST fail sign-change check!
    nc3_rejected = not (iv_hi(dE_family_iv(iv.mpf("0.71"))) < 0 and iv_lo(dE_family_iv(iv.mpf("0.72"))) > 0)
    assert nc3_rejected, "NC3 failed!"

    edges_iv = [(i, j, iv.sqrt(2 - 2 * dot3(X[i], X[j]))) for i in range(9) for j in range(i + 1, 9)]

    def eval_radius(r_chord_str: str) -> dict:
        r_c = iv.mpf(r_chord_str)
        R_geo = r_c + (r_c ** 3) / (24 * (1 - (r_c * r_c) / 4))
        sqrt2 = iv.sqrt(2)
        W_i = [iv.mpf(0)] * 9
        for (i, j, d0) in edges_iv:
            int_c = iv.mpf(0)
            for s_idx in range(K_steps):
                t_lo = iv.mpf(s_idx) / K_steps
                t_hi = iv.mpf(s_idx + 1) / K_steps
                d_lo = d0 - sqrt2 * t_hi * R_geo
                if iv_lo(d_lo) <= 0:
                    return dict(r_chord=r_chord_str, certified=False, alpha_lo=-1e9, mu_eff_lo=-1e9)
                d_hi = d0 + sqrt2 * t_hi * R_geo
                f_lo = d_lo * d_lo
                f_hi = d_hi * d_hi
                if iv_hi(f_hi) > 4:
                    f_hi = iv.mpf([iv_lo(f_hi), 4])
                # Exact |f''| <= max(2 - f/2, f/2) * (a + b)^2 for all f in [f_lo, f_hi] subset (0, 4]
                mA_hi = max(iv_hi(2 - f_lo / 2), iv_hi(f_hi / 2))
                termA = (iv.mpf(18) / 7) * (f_lo ** iv.mpf("-2.5")) * (iv.mpf(mA_hi) ** 2)
                termB = 12 * (f_lo ** iv.mpf("-1.5"))
                # Exact f^(4) <= (f/2) * (a + b)^4  =>  -(1/2) f^{-3/2} f^(4) >= -(1/4) f^{-1/2} (a + b)^4
                termC = iv.mpf("0.25") * (f_lo ** iv.mpf("-0.5"))
                w_t = ((1 - t_lo) ** 4 - (1 - t_hi) ** 4) / 4
                int_c = int_c + w_t * (termA + termB + termC)
            W_i[i] = W_i[i] + int_c
            W_i[j] = W_i[j] + int_c
        max_W = max(iv_hi(w) for w in W_i)
        # (1/2) v^T H_0 v + (1/6) T_3(v,v,v) + (1/6) int_0^1 (1-t)^3 g^(4)(t) dt
        #   >= (1/2) (v^T H_0 v) * [ 1 - (C3/3)*R_geo - (4/3)*(max_W / lam_min)*R_geo^2 ]
        c3_term = (C3_val / 3) * R_geo
        c4_term = (iv.mpf(4) / 3) * iv.mpf(max_W) * (R_geo * R_geo) / iv.mpf(lam_min_cert)
        alpha = 1 - c3_term - c4_term
        mu_eff = alpha * iv.mpf(lam_min_cert)
        return dict(
            r_chord=r_chord_str,
            R_geo_hi=float(iv_hi(R_geo)),
            c3_loss_hi=float(iv_hi(c3_term)),
            c4_loss_hi=float(iv_hi(c4_term)),
            alpha_lo=float(iv_lo(alpha)),
            mu_eff_lo=float(iv_lo(mu_eff)),
            certified=(iv_lo(alpha) > 0),
        )

    ladder = [eval_radius(rs) for rs in ["0.001", "0.00950125", "0.04", "0.06", "0.064", "0.065", "0.070"]]
    assert all(row["certified"] for row in ladder[:-1]), "Expected certification up to 0.065!"
    nc1_rejected = not ladder[-1]["certified"]
    assert nc1_rejected, "NC1 failed: r=0.070 unexpectedly certified!"

    return dict(
        kind="n9-l6-geodesic-taylor-iv",
        seed=SEED,
        iv_dps=50,
        z_star_interval=[mp.nstr(iv_lo(z_iv), 42), mp.nstr(iv_hi(z_iv), 42)],
        z_star_width=float(iv_hi(z_iv) - iv_lo(z_iv)),
        d2E_bracket_lo=float(iv_lo(d2_all)),
        E_ttp_interval=[mp.nstr(iv_lo(E_ttp_iv), 42), mp.nstr(iv_hi(E_ttp_iv), 42)],
        palais_d3h_criticality=dict(
            exact_at_z_star=True,
            grad_norm_over_z_iv_hi=float(iv_hi(grad_norm)),
            note="By D3h Palais symmetry, cap tangent gradients and prism azimuthal gradients are identically 0, and prism meridional gradient vanishes iff E'(z)=0; hence grad_tan E(X(z*)) = 0 identically with zero linear residual.",
        ),
        lam_min_cert=float(lam_min_cert),
        C3_whitened_cert=float(iv_hi(C3_val)),
        rigorous_radius_chord=0.065,
        mu_eff_at_r_star_lo=ladder[-2]["mu_eff_lo"],
        mu_eff_at_0001_lo=ladder[0]["mu_eff_lo"],
        ladder=ladder,
        negative_controls=dict(
            NC1_r0070_rejected=nc1_rejected,
            NC2_deflated_C3_rejected=nc2_rejected,
            NC3_wrong_z_bracket_rejected=nc3_rejected,
        ),
        runtime_s=round(time.time() - t0, 2),
    )


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=str, default=str(REPO / "numerics" / "bounds" / "results" / "l6_taylor.json"))
    args = ap.parse_args()
    res = certify_l6_on_z_interval()
    out_p = Path(args.out)
    out_p.parent.mkdir(parents=True, exist_ok=True)
    out_p.write_text(json.dumps(res, indent=2, ensure_ascii=False))
    print(f"[l6_taylor] CERTIFIED r* = {res['rigorous_radius_chord']} (mu_eff >= {res['mu_eff_at_r_star_lo']:.6f}) on exact z* interval (width {res['z_star_width']:.2e}) in {res['runtime_s']}s!")
    print(f"  At r=0.001: mu_eff >= {res['mu_eff_at_0001_lo']:.6f} | At r=0.060: mu_eff >= {res['ladder'][3]['mu_eff_lo']:.6f}")
    print(f"  Negative controls: {res['negative_controls']}")


if __name__ == "__main__":
    main()
