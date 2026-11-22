#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""stage_a_closure.py — Master Stage A Closure Verifier for Thomson N=9 (closed = true).

Verifies the complete, zero-gap mathematical proof of global optimality and uniqueness
up to O(3) x S_9 of the D_{3h} tricapped trigonal prism X_TTP(z*) for Thomson N=9
using the streamlined 5-slab + 1-cap architecture at a_0 = -9/10:

  Chain:  L0 ([-1, -9/10] exclusion via 5 slabs, tightest margin +9.70e-3)
       -> L1/L2 (m >= -9/10 exact rational S_3 3-point SDP M=10, K=10; gap = 9.96e-20)
       -> L3 (1D 50-dps interval coercivity: all 36 pairs in U_k [nu_k(z*) - 1e-6, nu_k(z*) + 1e-6])
       -> L4 (50-dps interval Gram det3/det4 + exhaustive K_9 DFS: 30,240 survivors == S_9 orbit of TTP)
       -> L5 (50-dps interval Procrustes + D_{3h} achirality O(3)->SO(3): d_P <= 1.488e-5 << r*)
       -> L6 (50-dps interval geodesic-Procrustes 4th-order Taylor on exact z* interval: r* = 0.06500)
       -> Global minimum & uniqueness (O(3) x S_9), closed = true.

Negative controls (all 5 must trigger):
  NC1: Tampered claimed_bound in M10K10 certificate rejected out-of-process.
  NC2: Inflated forcing gap (1e-15) breaks L3 1D interval coercivity at rho=1e-6.
  NC3: Inflated rho (1e-4) breaks sharp L4 16-K4 Gram rigidity.
  NC4: Exceeding radius r=0.070 rejected by L6 geodesic Taylor.
  NC5: Tampered PSD block diagonal (-10) in M10K10 certificate rejected out-of-process.

Usage:
  python3 numerics/bounds/stage_a_closure.py                # Full end-to-end verification (incl. all 11 certs)
  python3 numerics/bounds/stage_a_closure.py --fast-l0      # Skip out-of-process LDL^T on the 10 archived L0 certs
"""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import itertools
import json
import math
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

from mpmath import iv, mp

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
CERTS = REPO / "certificates"
RESULTS = HERE / "results"
OUT_JSON = RESULTS / "stage_a_closure.json"

sys.path.insert(0, str(HERE))
import l6_taylor  # noqa: E402

mp.dps = 55
iv.dps = 50

SEED = 20261120
RHO_STR = "1e-6"
CUTOFF_A0 = Fraction(-9, 10)
ENDGAME_FROZEN_SHA256 = "86863a09bf84e950e85fc5f902bc2b4046a87f06703bd782e5148fc119afd69f"

L0_SPECS = [
    ("[-1,-99/100]",      Fraction(-1),        Fraction(-99, 100),  "slab_band.py",    "n9-stage-a2-slab-sm1_m99o100.json"),
    ("[-99/100,-97/100]", Fraction(-99, 100),  Fraction(-97, 100),  "slab_band.py",    "n9-stage-a2-slab-sm99o100_m97o100.json"),
    ("[-97/100,-19/20]",  Fraction(-97, 100),  Fraction(-19, 20),   "slab_band.py",    "n9-stage-a2-slab-sm97o100_m19o20.json"),
    ("[-19/20,-91/100]",  Fraction(-19, 20),   Fraction(-91, 100),  "slab_band.py",    "n9-stage-a2-slab-sm19o20_m91o100.json"),
    ("[-91/100,-9/10]",   Fraction(-91, 100),  Fraction(-9, 10),    "slab_band.py",    "n9-stage-a2-slab-sm91o100_m9o10.json"),
]

MAIN_CERT = CERTS / "n9-stage-a-r24-symcap-m090_M10K10.json"


def iv_lo(x) -> mp.mpf:
    return mp.make_mpf(x._mpi_[0])


def iv_hi(x) -> mp.mpf:
    return mp.make_mpf(x._mpi_[1])


def frac_to_iv(q: Fraction):
    return iv.mpf(int(q.numerator)) / iv.mpf(int(q.denominator))


def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def code_version() -> str:
    try:
        return subprocess.check_output(
            ["git", "describe", "--always", "--dirty"], cwd=str(REPO),
            text=True, stderr=subprocess.DEVNULL
        ).strip()
    except Exception:
        return "unknown"


# ==============================================================================
# Exact TTP 6 Inner-Product Levels on z_iv
# ==============================================================================
def ttp_levels_iv(z_iv) -> tuple[list, list[int]]:
    """Return the 6 sorted exact inner-product intervals nu_0 < ... < nu_5 of X_TTP(z_iv)
    and their exact multiplicities (summing to 36)."""
    rho = iv.sqrt(1 - z_iv * z_iv)
    # Ordered levels for z* ~ 0.7036483958:
    #   nu_0 = -1/2 - (1/2) z^2            (6 pairs: opposite prism vertices across equator)
    #   nu_1 = -1/2                        (3 pairs: cap-cap)
    #   nu_2 = -(1/2) rho                  (12 pairs: non-adjacent cap-prism? Wait: let's compute directly from X_TTP!)
    # Compute directly from X_TTP(z_iv) so there is zero transcription error!
    X, _, _ = l6_taylor.build_ttp_and_basis_iv(z_iv)
    raw_dots = []
    for i in range(9):
        for j in range(i + 1, 9):
            d = l6_taylor.dot3(X[i], X[j])
            raw_dots.append((i, j, d))
    # Cluster by midpoint separation (> 1e-2 between distinct TTP levels)
    clusters: list[list] = []
    for i, j, d in raw_dots:
        mid = float((iv_lo(d) + iv_hi(d)) / 2)
        placed = False
        for cl in clusters:
            if abs(mid - cl[0]) < 1e-3:
                cl[1].append((i, j, d))
                placed = True
                break
        if not placed:
            clusters.append([mid, [(i, j, d)]])
    clusters.sort(key=lambda c: c[0])
    assert len(clusters) == 6, f"Expected 6 TTP levels, got {len(clusters)}"
    levels = []
    mults = []
    for _, items in clusters:
        lo = min(iv_lo(d) for _, _, d in items)
        hi = max(iv_hi(d) for _, _, d in items)
        levels.append(iv.mpf([lo, hi]))
        mults.append(len(items))
    assert sum(mults) == 36
    # Verify strict separation
    for k in range(5):
        assert iv_hi(levels[k]) < iv_lo(levels[k + 1]), f"Overlap between levels {k} and {k+1}"
    return levels, mults


# ==============================================================================
# L0: Exact Exclusion on [-1, -153/200]
# ==============================================================================
def _verify_one_l0(spec: tuple) -> dict:
    label, m_lo_exp, m_hi_exp, script_name, cert_name = spec
    cpath = CERTS / cert_name
    assert cpath.exists(), f"Missing L0 cert {cpath}"
    raw = json.loads(cpath.read_text())
    m_lo = Fraction(raw["m_lo"])
    m_hi = Fraction(raw["m_hi"])
    assert m_lo == m_lo_exp and m_hi == m_hi_exp, f"{cert_name}: interval [{m_lo},{m_hi}] != [{m_lo_exp},{m_hi_exp}]"
    bound = Fraction(raw["claimed_bound"])
    t0 = time.time()
    proc = subprocess.run(
        [sys.executable, str(HERE / script_name), "--verify-cert", str(cpath)],
        capture_output=True, text=True, cwd=str(REPO),
    )
    dt = time.time() - t0
    assert proc.returncode == 0, f"L0 verifier failed on {cert_name} (rc={proc.returncode}): {proc.stdout}\n{proc.stderr}"
    return dict(
        region=label, m_lo=str(m_lo), m_hi=str(m_hi),
        cert=f"certificates/{cert_name}", verifier=script_name,
        sha256=sha256_file(cpath),
        claimed_bound=f"{bound.numerator}/{bound.denominator}",
        claimed_bound_float=float(bound),
        verified_out_of_process=True,
        verify_s=round(dt, 2),
    )


def verify_l0(E_ttp_hi: mp.mpf, fast_l0: bool = False) -> dict:
    t0 = time.time()
    # Verify exact partition contiguity first
    assert L0_SPECS[0][1] == Fraction(-1)
    assert L0_SPECS[-1][2] == CUTOFF_A0
    for i in range(len(L0_SPECS) - 1):
        assert L0_SPECS[i][2] == L0_SPECS[i + 1][1], f"Gap between L0 piece {i} and {i+1}"

    if fast_l0:
        rows = []
        for label, m_lo_exp, m_hi_exp, script_name, cert_name in L0_SPECS:
            cpath = CERTS / cert_name
            raw = json.loads(cpath.read_text())
            assert Fraction(raw["m_lo"]) == m_lo_exp and Fraction(raw["m_hi"]) == m_hi_exp
            bound = Fraction(raw["claimed_bound"])
            rows.append(dict(
                region=label, m_lo=str(m_lo_exp), m_hi=str(m_hi_exp),
                cert=f"certificates/{cert_name}", verifier=script_name,
                sha256=sha256_file(cpath),
                claimed_bound=f"{bound.numerator}/{bound.denominator}",
                claimed_bound_float=float(bound),
                verified_out_of_process=False, verify_s=0.0,
            ))
    else:
        with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:
            rows = list(ex.map(_verify_one_l0, L0_SPECS))

    min_margin = mp.inf
    tightest = None
    for row in rows:
        b_iv = frac_to_iv(Fraction(row["claimed_bound"]))
        margin = iv_lo(b_iv) - E_ttp_hi
        assert margin > 0, f"L0 piece {row['region']} bound <= E_TTP_hi! margin={margin}"
        row["margin_above_E_ttp_hi"] = float(margin)
        if margin < min_margin:
            min_margin = margin
            tightest = row["region"]

    return dict(
        ok=True,
        covered_interval="[-1, -9/10]",
        n_pieces=len(rows),
        all_verified_out_of_process=not fast_l0,
        tightest_piece=tightest,
        min_margin_above_E_ttp_hi=float(min_margin),
        runtime_s=round(time.time() - t0, 2),
        pieces=rows,
    )


# ==============================================================================
# L1 + L2: Exact Rational S3 Cap Certificate on [-153/200, 1]
# ==============================================================================
def verify_l1_l2(E_ttp_hi: mp.mpf) -> tuple[dict, list[Fraction], Fraction, mp.mpf]:
    t0 = time.time()
    assert MAIN_CERT.exists(), f"Missing main R24 certificate {MAIN_CERT}"
    proc = subprocess.run(
        [sys.executable, str(HERE / "sym_cap_sdpa.py"), "--verify-cert", str(MAIN_CERT)],
        capture_output=True, text=True, cwd=str(REPO),
    )
    assert proc.returncode == 0, f"Main cert verify failed: {proc.stdout}\n{proc.stderr}"
    vout = json.loads(proc.stdout)
    assert vout["ok"] is True
    assert vout["n"] == 9
    assert Fraction(vout["a0"]) == CUTOFF_A0
    assert vout["identity_error"] == 0

    raw = json.loads(MAIN_CERT.read_text())
    h_d = [Fraction(x) for x in raw["h"]]
    R1 = Fraction(raw["R1"])
    R2 = Fraction(raw["R2"])
    cert_exact = Fraction(raw["claimed_bound"])
    assert Fraction(vout["certified_exact"]) == cert_exact

    cert_iv = frac_to_iv(cert_exact)
    eps_forcing_hi = E_ttp_hi - iv_lo(cert_iv)
    assert eps_forcing_hi > 0, f"Certified bound exceeds E_TTP_hi! Impossible: {eps_forcing_hi}"
    assert eps_forcing_hi < mp.mpf("1.5e-19"), f"Forcing gap too large: {eps_forcing_hi}"

    summary = dict(
        ok=True,
        cert=f"certificates/{MAIN_CERT.name}",
        sha256=vout["sha256"],
        n=vout["n"], a0=vout["a0"], M=vout["M"], K=vout["K"],
        round_bits=raw["round_bits"],
        blocks_verified=vout["blocks_verified"],
        identity_error=vout["identity_error"],
        R1=float(R1), R2=float(R2),
        certified_exact=vout["certified_exact"],
        certified_float=float(cert_exact),
        eps_forcing_hi=float(eps_forcing_hi),
        eps_forcing_hi_str=mp.nstr(eps_forcing_hi, 15),
        verify_s=round(time.time() - t0, 2),
    )
    return summary, h_d, R2, eps_forcing_hi


# ==============================================================================
# L3: 1D 50-dps Interval Coercivity (Centered 2nd-Order Taylor Bisection)
# ==============================================================================
def verify_l3(h_d: list[Fraction], R2: Fraction, eps_forcing_hi: mp.mpf,
              levels_iv: list, rho_str: str = RHO_STR) -> dict:
    """Prove phi(t) - H(t)/(1+R2) > eps_forcing_hi for ALL t in [-153/200, 1) outside
    U_{k=0}^5 [nu_k(z_iv) - rho, nu_k(z_iv) + rho]."""
    t0 = time.time()
    inv_1pR2 = iv.mpf(1) / (iv.mpf(1) + frac_to_iv(R2))
    h_iv = [frac_to_iv(c) * inv_1pR2 for c in h_d]
    hp_iv = [h_iv[k] * k for k in range(1, len(h_iv))]
    hpp_iv = [hp_iv[k] * k for k in range(1, len(hp_iv))]

    def poly_eval(coeffs, x):
        acc = iv.mpf(0)
        for c in reversed(coeffs):
            acc = acc * x + c
        return acc

    def g_val(x):
        return (2 - 2 * x) ** (-iv.mpf("0.5")) - poly_eval(h_iv, x)

    def g_d1(x):
        return (2 - 2 * x) ** (-iv.mpf("1.5")) - poly_eval(hp_iv, x)

    def g_d2(x):
        return 3 * (2 - 2 * x) ** (-iv.mpf("2.5")) - poly_eval(hpp_iv, x)

    def g_taylor_box(a: mp.mpf, b: mp.mpf):
        mid = (a + b) / 2
        hw = (b - a) / 2
        m_iv = iv.mpf(mid)
        box = iv.mpf([a, b])
        # First check monotonicity: if g'(box) has definite sign, endpoints suffice!
        d1_box = g_d1(box)
        if iv_lo(d1_box) >= 0:
            return g_val(iv.mpf(a))
        if iv_hi(d1_box) <= 0:
            return g_val(iv.mpf(b))
        # Centered 2nd-order Taylor form over [a, b]
        return g_val(m_iv) + g_d1(m_iv) * iv.mpf([-hw, hw]) + iv.mpf("0.5") * g_d2(box) * iv.mpf([0, hw * hw])

    # Analytic tail [0.99, 1): phi(t) >= (2 - 2*0.99)^(-1/2) = 1/sqrt(0.02), |H(t)/(1+R2)| <= sum |h_iv[k]|
    t_tail = mp.mpf("0.99")
    phi_tail_lo = iv_lo((2 - 2 * iv.mpf(t_tail)) ** (-iv.mpf("0.5")))
    H_abs_hi = sum(max(abs(iv_lo(c)), abs(iv_hi(c))) for c in h_iv)
    tail_gap_lo = phi_tail_lo - H_abs_hi
    assert tail_gap_lo > eps_forcing_hi, f"Analytic tail [0.99, 1) failed: {tail_gap_lo} <= {eps_forcing_hi}"

    rho = mp.mpf(rho_str)
    # Build the 7 complement segments inside [a0, 0.99]:
    # Excluded band k is [iv_lo(levels_iv[k]) - rho, iv_hi(levels_iv[k]) + rho],
    # which STRICTLY CONTAINS [nu_k(z*) - rho, nu_k(z*) + rho] for every z* in z_iv!
    # Wait: to prove t_ij in [nu_k(z*) - rho, nu_k(z*) + rho] for the TRUE z*,
    # we must exclude ONLY the INNER intersection [iv_hi(levels_iv[k]) - rho, iv_lo(levels_iv[k]) + rho],
    # because if t lies in [iv_hi - rho, iv_lo + rho], then for EVERY z in z_iv:
    #   nu_k(z) - rho <= iv_hi - rho <= t <= iv_lo + rho <= nu_k(z) + rho => |t - nu_k(z)| <= rho!
    cuts = []
    for k, lv in enumerate(levels_iv):
        band_lo = iv_hi(lv) - rho
        band_hi = iv_lo(lv) + rho
        assert band_lo < band_hi, f"Level {k} width exceeds 2*rho!"
        cuts.append((band_lo, band_hi))

    a0_mp = iv_lo(frac_to_iv(CUTOFF_A0))
    segs = [(a0_mp, cuts[0][0])]
    for k in range(5):
        segs.append((cuts[k][1], cuts[k + 1][0]))
    segs.append((cuts[5][1], t_tail))

    total_boxes = 0
    global_min_lo = tail_gap_lo
    seg_reports = []
    ok = True

    for s_idx, (sa, sb) in enumerate(segs):
        assert sa < sb
        stack = [(sa, sb)]
        seg_boxes = 0
        seg_min = mp.inf
        while stack:
            a, b = stack.pop()
            seg_boxes += 1
            if seg_boxes > 200000:
                ok = False
                break
            val = g_taylor_box(a, b)
            vlo = iv_lo(val)
            vhi = iv_hi(val)
            if vlo > eps_forcing_hi:
                if vlo < seg_min:
                    seg_min = vlo
            elif vhi <= eps_forcing_hi:
                # Definitely fails coercivity at this box!
                ok = False
                if vlo < seg_min:
                    seg_min = vlo
                break
            else:
                if b - a < mp.mpf("1e-35"):
                    ok = False
                    break
                mid = (a + b) / 2
                stack.append((mid, b))
                stack.append((a, mid))
        total_boxes += seg_boxes
        if seg_min < global_min_lo:
            global_min_lo = seg_min
        seg_reports.append(dict(
            seg=s_idx, a=float(sa), b=float(sb),
            boxes=seg_boxes, min_gap_lo=float(seg_min),
            margin_factor=float(seg_min / eps_forcing_hi) if eps_forcing_hi > 0 else 0.0,
        ))
        if not ok:
            break

    return dict(
        ok=ok and (global_min_lo > eps_forcing_hi),
        rho=float(rho),
        eps_forcing_hi=float(eps_forcing_hi),
        min_gap_lo=float(global_min_lo),
        margin_factor=float(global_min_lo / eps_forcing_hi),
        analytic_tail_099_1_lo=float(tail_gap_lo),
        total_boxes=total_boxes,
        runtime_s=round(time.time() - t0, 2),
        segments=seg_reports,
    )


# ==============================================================================
# L4: 50-dps Interval Gram det3/det4 + Exhaustive K_9 Backtracking DFS
# ==============================================================================
def _iv_det3(a, b, c):
    return 1 + 2 * a * b * c - a ** 2 - b ** 2 - c ** 2


def _iv_det4(g01, g02, g03, g12, g13, g23):
    # Exact 4x4 Gram determinant with 1s on diagonal (for 4 points in R^3, det4 == 0 identically!)
    s2 = g01 ** 2 + g02 ** 2 + g03 ** 2 + g12 ** 2 + g13 ** 2 + g23 ** 2
    s3 = 2 * (g01 * g02 * g12 + g01 * g03 * g13 + g02 * g03 * g23 + g12 * g13 * g23)
    s4a = (g01 * g23) ** 2 + (g02 * g13) ** 2 + (g03 * g12) ** 2
    s4b = 2 * (g01 * g02 * g13 * g23 + g01 * g03 * g12 * g23 + g02 * g03 * g12 * g13)
    return 1 - s2 + s3 + s4a - s4b


def _canon_k4(tup: tuple[int, int, int, int, int, int]) -> tuple[int, int, int, int, int, int]:
    # Edge order: (0,1),(0,2),(0,3),(1,2),(1,3),(2,3)
    edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    eidx = {e: k for k, e in enumerate(edges)}
    best = None
    for p in itertools.permutations(range(4)):
        mapped = tuple(tup[eidx[(min(p[u], p[v]), max(p[u], p[v]))]] for u, v in edges)
        if best is None or mapped < best:
            best = mapped
    return best


def verify_l4(levels_iv: list, z_iv, rho_str: str = RHO_STR, run_dfs: bool = True) -> dict:
    t0 = time.time()
    rho = mp.mpf(rho_str)
    # Outer interval for band k: covers EVERY t with |t - nu_k(z*)| <= rho for z* in z_iv
    bands = [iv.mpf([iv_lo(lv) - rho, iv_hi(lv) + rho]) for lv in levels_iv]

    # Step 1: 3x3 Gram det >= 0 across all C(6+2, 3) = 56 unordered color triples
    valid_triples = set()
    for a in range(6):
        for b in range(a, 6):
            for c in range(b, 6):
                d3 = _iv_det3(bands[a], bands[b], bands[c])
                if iv_hi(d3) >= 0:
                    valid_triples.add((a, b, c))

    # Step 2: 4x4 Gram det >= 0 across all canonical K_4 colorings whose 4 faces are valid triples
    canon_tested = set()
    canon_valid = set()
    all_valid_k4_labeled = set()

    # Enumerate canonical K_4s efficiently using valid triples on (0,1,2) + (0,1,3) + (0,2,3) + (1,2,3)
    tri_ord = set()
    for a, b, c in valid_triples:
        for p in itertools.permutations((a, b, c)):
            tri_ord.add(p)

    # Index valid triples by first edge (a,b) -> list of c
    tri_by_ab: dict[tuple[int, int], list[int]] = {}
    for a, b, c in tri_ord:
        tri_by_ab.setdefault((a, b), []).append(c)

    for g01 in range(6):
        for g02 in range(6):
            for g12 in tri_by_ab.get((g01, g02), []):
                for g03 in range(6):
                    for g13 in tri_by_ab.get((g01, g03), []):
                        for g23 in tri_by_ab.get((g02, g03), []):
                            if (g12, g13, g23) not in tri_ord:
                                continue
                            tup = (g01, g02, g03, g12, g13, g23)
                            ck = _canon_k4(tup)
                            if ck not in canon_tested:
                                canon_tested.add(ck)
                                d4 = _iv_det4(bands[ck[0]], bands[ck[1]], bands[ck[2]],
                                              bands[ck[3]], bands[ck[4]], bands[ck[5]])
                                # 4 vectors in R^3 are linearly dependent => exact det(G_4) == 0!
                                if iv_lo(d4) <= 0 <= iv_hi(d4):
                                    canon_valid.add(ck)
                            if ck in canon_valid:
                                all_valid_k4_labeled.add(tup)

    result = dict(
        rho=float(rho),
        valid_triples=len(valid_triples),
        k4_canonical_tested=len(canon_tested),
        k4_canonical_valid=len(canon_valid),
        k4_labeled_valid=len(all_valid_k4_labeled),
    )

    if not run_dfs:
        result["runtime_s"] = round(time.time() - t0, 2)
        return result

    assert len(valid_triples) == 45, f"Expected 45 valid triples, got {len(valid_triples)}"
    assert len(canon_valid) == 16, f"Expected 16 canonical K4s, got {len(canon_valid)}"

    # Step 3: Full exhaustive K_9 backtracking DFS (vertex-by-vertex, checking all K_4s)
    # Build fast lookup tables:
    # For a triangle (c_ij, c_ik, c_jk) in tri_ord, what colors (c_iv, c_jv, c_kv) form a valid K_4?
    k4_ext: dict[tuple[int, int, int], list[tuple[int, int, int]]] = {}
    for g01, g02, g03, g12, g13, g23 in all_valid_k4_labeled:
        k4_ext.setdefault((g01, g02, g12), []).append((g03, g13, g23))

    # For faster incremental checking when adding vertex v (0..8), color matrix C[i][j] (i<j):
    # Precompute bitmask of allowed c_kv given (c_ij, c_ik, c_jk, c_iv, c_jv)
    ext_mask: dict[tuple[int, int, int, int, int], int] = {}
    for g01, g02, g03, g12, g13, g23 in all_valid_k4_labeled:
        key = (g01, g02, g12, g03, g13)
        ext_mask[key] = ext_mask.get(key, 0) | (1 << g23)

    tri_mask: dict[tuple[int, int], int] = {}
    for a, b, c in tri_ord:
        tri_mask[(a, b)] = tri_mask.get((a, b), 0) | (1 << c)

    # Represent each 9-vertex coloring as a 36-tuple of ints in 0..5
    pairs9 = [(i, j) for i in range(9) for j in range(i + 1, 9)]
    C = [[-1] * 9 for _ in range(9)]
    survivors: list[tuple[int, ...]] = []

    def assign_edges(v: int, u: int):
        """Assign C[u][v] for u = 0 .. v-1."""
        if u == v:
            if v == 8:
                survivors.append(tuple(C[i][j] for i, j in pairs9))
                return
            assign_edges(v + 1, 0)
            return
        # Allowed colors for C[u][v]
        mask = 0b111111
        if u >= 1:
            # Must satisfy triangles (a, u, v) for all a < u
            for a in range(u):
                mask &= tri_mask.get((C[a][u], C[a][v]), 0)
                if not mask:
                    return
        if u >= 2:
            # Must satisfy K_4 (a, b, u, v) for all 0 <= a < b < u
            for a in range(u):
                ca_u = C[a][u]
                ca_v = C[a][v]
                for b in range(a + 1, u):
                    mask &= ext_mask.get((C[a][b], ca_u, C[b][u], ca_v, C[b][v]), 0)
                    if not mask:
                        return
        # Try each surviving bit
        m = mask
        while m:
            lsb = m & -m
            col = lsb.bit_length() - 1
            m ^= lsb
            C[u][v] = col
            assign_edges(v, u + 1)

    assign_edges(1, 0)

    # Build exact S_9 orbit of TTP coloring
    X_ttp, _, _ = l6_taylor.build_ttp_and_basis_iv(z_iv)
    ttp_C = [[0] * 9 for _ in range(9)]
    for i in range(9):
        for j in range(i + 1, 9):
            d = l6_taylor.dot3(X_ttp[i], X_ttp[j])
            mid = (iv_lo(d) + iv_hi(d)) / 2
            matches = [k for k, b in enumerate(bands) if iv_lo(b) <= mid <= iv_hi(b)]
            assert len(matches) == 1
            ttp_C[i][j] = ttp_C[j][i] = matches[0]

    ttp_orbit = set()
    for perm in itertools.permutations(range(9)):
        ttp_orbit.add(tuple(ttp_C[perm[i]][perm[j]] for i, j in pairs9))

    surv_set = set(survivors)
    assert len(survivors) == len(surv_set) == 30240, f"Expected 30240 survivors, got {len(survivors)}"
    assert len(ttp_orbit) == 30240, f"Expected |S_9/D_3h|=30240, got {len(ttp_orbit)}"
    assert surv_set == ttp_orbit, "Survivor set does NOT equal S_9 orbit of TTP!"

    result.update(
        ok=True,
        k9_survivors=len(survivors),
        ttp_s9_orbit_size=len(ttp_orbit),
        survivor_set_equals_ttp_orbit=True,
        runtime_s=round(time.time() - t0, 2),
    )
    return result


# ==============================================================================
# L5: Direct 50-dps Interval Procrustes + D_{3h} Achirality (O(3) -> SO(3))
# ==============================================================================
def verify_l5(z_iv, rho_str: str = RHO_STR) -> dict:
    """Certify d_{P,SO(3)}(Y, sigma*X_TTP(z*)) <= C_L5 * rho directly in 50-dps iv."""
    t0 = time.time()
    X, _, _ = l6_taylor.build_ttp_and_basis_iv(z_iv)

    # Verify S = X^T X = diag(9/2 - 3 z^2, 9/2 - 3 z^2, 6 z^2) in 50-dps iv
    S = [[sum(X[i][a] * X[i][b] for i in range(9)) for b in range(3)] for a in range(3)]
    lam_xy = iv.mpf("4.5") - 3 * (z_iv ** 2)
    lam_z = 6 * (z_iv ** 2)
    # Check off-diagonals contain 0 and diagonals contain exact formulas
    for a in range(3):
        for b in range(3):
            if a != b:
                assert iv_lo(S[a][b]) <= 0 <= iv_hi(S[a][b]), f"S[{a}][{b}] not zero!"
            else:
                target = lam_xy if a < 2 else lam_z
                diff = S[a][a] - target
                assert iv_lo(diff) <= 0 <= iv_hi(diff), f"S[{a}][{a}] mismatch!"

    # Verify exact D_{3h} achirality: J = diag(1, 1, -1) satisfies X * J = pi_{sigma_h} * X
    # where pi_{sigma_h} swaps prism k <-> k+3 (k=0,1,2) and fixes caps 6,7,8.
    perm_sh = [3, 4, 5, 0, 1, 2, 6, 7, 8]
    for i in range(9):
        xj = [X[i][0], X[i][1], -X[i][2]]
        xp = X[perm_sh[i]]
        for c in range(3):
            diff = xj[c] - xp[c]
            assert iv_lo(diff) <= 0 <= iv_hi(diff), f"Achirality check failed at ({i},{c})"

    # Eigenvalue bounds: lam_1 = lam_xy > lam_3 = lam_z > 0
    assert iv_lo(lam_xy) > iv_hi(lam_z) > 0
    lam1_hi = iv.mpf(iv_hi(lam_xy))
    lam3_lo = iv.mpf(iv_lo(lam_z))
    sig1_hi = iv.sqrt(lam1_hi)
    sig3_lo = iv.sqrt(lam3_lo)

    rho = iv.mpf(rho_str)
    eta_hi = iv.sqrt(72) * rho
    beta_hi = lam1_hi * eta_hi / (lam3_lo * lam3_lo)
    beta_thresh = min(iv.mpf("0.5"), sig3_lo / (2 * sig1_hi))
    assert iv_hi(beta_hi) < iv_lo(beta_thresh), f"Procrustes beta threshold exceeded: {beta_hi} vs {beta_thresh}"

    C_L5 = iv.sqrt(72) * ((sig1_hi ** 3) / (lam3_lo * lam3_lo) + 2 / sig3_lo)
    dP_bound_hi = iv_hi(C_L5 * rho)
    # Conservative Lean 4 TableB5Uncond.lean Route A cross-check: C_A = 18.957127, delta_A = 0.014588
    dP_lean_routeA_hi = float(mp.mpf("18.957127") * mp.mpf(rho_str))

    return dict(
        ok=True,
        lam1_hi=float(iv_hi(lam1_hi)),
        lam3_lo=float(iv_lo(lam3_lo)),
        beta_hi=float(iv_hi(beta_hi)),
        beta_thresh_lo=float(iv_lo(beta_thresh)),
        achirality_O3_to_SO3_verified=True,
        C_L5_hi=float(iv_hi(C_L5)),
        dP_SO3_bound_hi=float(dP_bound_hi),
        dP_lean_routeA_hi=dP_lean_routeA_hi,
        runtime_s=round(time.time() - t0, 2),
    )


# ==============================================================================
# Negative Controls NC1..NC5
# ==============================================================================
def run_negative_controls(h_d: list[Fraction], R2: Fraction, levels_iv: list,
                          z_iv, l6_res: dict) -> dict:
    t0 = time.time()
    raw_cert = json.loads(MAIN_CERT.read_text())

    # NC1: Tamper claimed_bound (+1e-9) -> sym_cap_sdpa.py --verify-cert MUST fail
    with tempfile.TemporaryDirectory() as td:
        p1 = Path(td) / "nc1_tampered_bound.json"
        c1 = dict(raw_cert)
        cb = Fraction(raw_cert["claimed_bound"]) + Fraction(1, 10 ** 9)
        c1["claimed_bound"] = f"{cb.numerator}/{cb.denominator}"
        p1.write_text(json.dumps(c1))
        r1 = subprocess.run(
            [sys.executable, str(HERE / "sym_cap_sdpa.py"), "--verify-cert", str(p1), "--no-identity-check"],
            capture_output=True, text=True, cwd=str(REPO),
        )
        nc1_ok = (r1.returncode != 0)

        # NC5: Tamper PSD diagonal entry of F_0[0][0] -> -10 -> MUST fail exact LDL^T
        p5 = Path(td) / "nc5_tampered_psd.json"
        c5 = json.loads(MAIN_CERT.read_text())
        c5["blocks"][0]["utri"][0][0] = "-10"
        p5.write_text(json.dumps(c5))
        r5 = subprocess.run(
            [sys.executable, str(HERE / "sym_cap_sdpa.py"), "--verify-cert", str(p5), "--no-identity-check"],
            capture_output=True, text=True, cwd=str(REPO),
        )
        nc5_ok = (r5.returncode != 0)

    # NC2: Inflated eps_forcing = 1e-15 MUST fail L3 coercivity at rho = 1e-6
    l3_bad = verify_l3(h_d, R2, mp.mpf("1e-15"), levels_iv, rho_str=RHO_STR)
    nc2_ok = (l3_bad["ok"] is False)

    # NC3: Inflated rho = 1e-4 MUST break sharp L4 16-K4 rigidity (admits > 16 canonical K4s)
    l4_bad = verify_l4(levels_iv, z_iv, rho_str="1e-4", run_dfs=False)
    nc3_ok = (l4_bad["k4_canonical_valid"] > 16)

    # NC4: r = 0.070 MUST be rejected by L6 geodesic Taylor
    nc4_ok = bool(l6_res["negative_controls"]["NC1_r0070_rejected"])

    assert nc1_ok, "NC1 FAILED: tampered claimed_bound was NOT rejected!"
    assert nc2_ok, "NC2 FAILED: inflated eps_forcing=1e-15 unexpectedly passed L3!"
    assert nc3_ok, f"NC3 FAILED: inflated rho=1e-4 had k4_valid={l4_bad['k4_canonical_valid']} <= 16!"
    assert nc4_ok, "NC4 FAILED: r=0.070 was NOT rejected by L6!"
    assert nc5_ok, "NC5 FAILED: tampered PSD diagonal was NOT rejected!"

    return dict(
        all_triggered=True,
        NC1_tampered_bound_rejected=nc1_ok,
        NC2_inflated_eps_1e15_breaks_L3=nc2_ok,
        NC3_inflated_rho_1e4_breaks_L4_16K4=nc3_ok,
        NC3_observed_k4_at_1e4=l4_bad["k4_canonical_valid"],
        NC4_r0070_rejected_by_L6=nc4_ok,
        NC5_tampered_psd_rejected=nc5_ok,
        runtime_s=round(time.time() - t0, 2),
    )


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--fast-l0", action="store_true",
                    help="Skip re-running out-of-process LDL^T on the 10 archived L0 certificates")
    args = ap.parse_args()

    t_all = time.time()
    print("=" * 78)
    print("THOMSON N=9 — STAGE A COMPLETE CLOSURE VERIFIER (Round 24)")
    print("=" * 78)

    # Frozen historical ledger check
    endgame_path = RESULTS / "endgame.json"
    endgame_sha = sha256_file(endgame_path)
    assert endgame_sha == ENDGAME_FROZEN_SHA256, (
        f"Frozen endgame.json SHA-256 drifted: {endgame_sha} != {ENDGAME_FROZEN_SHA256}"
    )
    print(f"[0] Frozen endgame.json intact (sha256={endgame_sha[:16]}...)")

    # Exact z* and E_TTP(z*) interval isolation
    z_iv, d2_all = l6_taylor.isolate_z_star()
    E_ttp_iv = l6_taylor.E_family_iv(z_iv)
    E_ttp_lo = iv_lo(E_ttp_iv)
    E_ttp_hi = iv_hi(E_ttp_iv)
    levels_iv, mults = ttp_levels_iv(z_iv)
    print(f"[z*] z* in [{mp.nstr(iv_lo(z_iv), 42)}, {mp.nstr(iv_hi(z_iv), 42)}] (width={float(iv_hi(z_iv)-iv_lo(z_iv)):.2e})")
    print(f"[E*] E_TTP(z*) in [{mp.nstr(E_ttp_lo, 42)}, {mp.nstr(E_ttp_hi, 42)}]")

    # L0
    print(f"[L0] Verifying {len(L0_SPECS)} exact certificates covering [-1, -9/10] (fast_l0={args.fast_l0})...", flush=True)
    l0_res = verify_l0(E_ttp_hi, fast_l0=args.fast_l0)
    print(f"[L0] PASS in {l0_res['runtime_s']}s | tightest={l0_res['tightest_piece']} margin=+{l0_res['min_margin_above_E_ttp_hi']:.3e}")

    # L1 + L2
    print("[L1+L2] Verifying R24 exact rational M=10, K=10 certificate on [-9/10, 1]...", flush=True)
    l12_res, h_d, R2, eps_forcing_hi = verify_l1_l2(E_ttp_hi)
    print(f"[L1+L2] PASS in {l12_res['verify_s']}s | certified={l12_res['certified_float']:.15f} | eps_forcing<={l12_res['eps_forcing_hi']:.3e} | id_err=0")

    # L3
    print("[L3] Running 50-dps interval 1D coercivity on [-9/10, 1) outside rho=1e-6 bands...", flush=True)
    l3_res = verify_l3(h_d, R2, eps_forcing_hi, levels_iv, rho_str=RHO_STR)
    assert l3_res["ok"], f"L3 FAILED: {l3_res}"
    print(f"[L3] PASS in {l3_res['runtime_s']}s | boxes={l3_res['total_boxes']} | min_gap={l3_res['min_gap_lo']:.3e} ({l3_res['margin_factor']:.2f}x eps_forcing)")

    # L4
    print("[L4] Running 50-dps interval Gram det3/det4 + exhaustive K_9 DFS at rho=1e-6...", flush=True)
    l4_res = verify_l4(levels_iv, z_iv, rho_str=RHO_STR, run_dfs=True)
    assert l4_res["ok"], f"L4 FAILED: {l4_res}"
    print(f"[L4] PASS in {l4_res['runtime_s']}s | triples={l4_res['valid_triples']} | K4={l4_res['k4_canonical_valid']} | K9={l4_res['k9_survivors']} == TTP S_9 orbit")

    # L5
    print("[L5] Certifying 50-dps interval Procrustes + D_3h achirality (O(3)->SO(3))...", flush=True)
    l5_res = verify_l5(z_iv, rho_str=RHO_STR)
    assert l5_res["ok"]
    print(f"[L5] PASS in {l5_res['runtime_s']}s | C_L5<={l5_res['C_L5_hi']:.6f} | d_P,SO(3)<={l5_res['dP_SO3_bound_hi']:.3e} (Lean Route A: {l5_res['dP_lean_routeA_hi']:.3e})")

    # L6
    print("[L6] Certifying 50-dps interval geodesic-Procrustes 4th-order Taylor on z_iv...", flush=True)
    l6_res = l6_taylor.certify_l6_on_z_interval()
    r_star = l6_res["rigorous_radius_chord"]
    assert l5_res["dP_SO3_bound_hi"] < r_star and l5_res["dP_lean_routeA_hi"] < r_star
    ratio_l5_l6 = r_star / l5_res["dP_SO3_bound_hi"]
    ratio_lean = r_star / l5_res["dP_lean_routeA_hi"]
    print(f"[L6] PASS in {l6_res['runtime_s']}s | r*={r_star} (mu_eff>={l6_res['mu_eff_at_r_star_lo']:.6f}) | L6/L5 margin={ratio_l5_l6:.0f}x (Lean Route A: {ratio_lean:.0f}x)")

    # Negative controls NC1..NC5
    print("[NC] Running 5 negative controls (NC1..NC5)...", flush=True)
    nc_res = run_negative_controls(h_d, R2, levels_iv, z_iv, l6_res)
    print(f"[NC] PASS 5/5 in {nc_res['runtime_s']}s: { {k: v for k, v in nc_res.items() if k.startswith('NC')} }")

    closed = bool(
        l0_res["ok"] and l12_res["ok"] and l3_res["ok"]
        and l4_res["ok"] and l5_res["ok"]
        and (l5_res["dP_SO3_bound_hi"] < r_star)
        and nc_res["all_triggered"]
    )
    assert closed is True

    report = dict(
        kind="n9-stage-a-closure-round24",
        closed=True,
        uniqueness_proved=True,
        stage_a_full_certificate_reverify=not args.fast_l0,
        seed=SEED,
        code_version=code_version(),
        timestamp_utc=datetime.now(timezone.utc).isoformat(),
        endgame_frozen_sha256=endgame_sha,
        global_minimum=dict(
            configuration="D_3h tricapped trigonal prism X_TTP(z*)",
            uniqueness_group="O(3) x S_9",
            z_star_interval=[mp.nstr(iv_lo(z_iv), 42), mp.nstr(iv_hi(z_iv), 42)],
            E_ttp_interval=[mp.nstr(E_ttp_lo, 42), mp.nstr(E_ttp_hi, 42)],
            ttp_inner_product_levels=[
                dict(index=k, mult=mults[k], interval=[mp.nstr(iv_lo(lv), 30), mp.nstr(iv_hi(lv), 30)])
                for k, lv in enumerate(levels_iv)
            ],
        ),
        chain=dict(
            L0_exclusion=l0_res,
            L1_L2_symcap_M10K10=l12_res,
            L3_interval_coercivity=l3_res,
            L4_combinatorial_rigidity=l4_res,
            L5_procrustes_alignment=l5_res,
            L6_geodesic_taylor=dict(
                rigorous_radius_chord=r_star,
                lam_min_cert=l6_res["lam_min_cert"],
                C3_whitened_cert=l6_res["C3_whitened_cert"],
                mu_eff_at_r_star_lo=l6_res["mu_eff_at_r_star_lo"],
                mu_eff_at_0001_lo=l6_res["mu_eff_at_0001_lo"],
                palais_d3h_criticality=l6_res["palais_d3h_criticality"],
                margin_over_L5=round(ratio_l5_l6, 1),
                margin_over_Lean_RouteA=round(ratio_lean, 1),
                runtime_s=l6_res["runtime_s"],
            ),
        ),
        negative_controls=nc_res,
        total_runtime_s=round(time.time() - t_all, 2),
    )

    OUT_JSON.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print("=" * 78)
    print(f"STAGE A CLOSED = TRUE (Global Optimality + O(3) x S_9 Uniqueness CERTIFIED!)")
    print(f"Report written -> {OUT_JSON}  (total {report['total_runtime_s']}s)")
    print("=" * 78)


if __name__ == "__main__":
    main()
