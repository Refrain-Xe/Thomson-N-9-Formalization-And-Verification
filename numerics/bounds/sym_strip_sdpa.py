#!/usr/bin/env python3
"""Exact rational (Fraction) S2/S2/S3-symmetry-reduced (2,7) pole-ring typed strip/narrow-cap SDP
for Thomson N=9 with full K up to M, SDPA-GMP 7.1.3 export, and exact dyadic+LDL^T certification.

Symmetry exploitation:
  - lambda_A (PPR, u=t_01 in [lo, hi], v,t in [lo, 1]): S2-symmetric in v <-> t
  - lambda_B (PRR, u,v=t_pr, t=t_rr in [lo, 1]):        S2-symmetric in u <-> v
  - lambda_G (RRR, u,v,t in [lo, 1]):                   S3-symmetric in (u, v, t)
Reduces constraint rows by ~2.2x and PSD block sizes by ~2x (~15-30x faster in SDPA-GMP than strips_final.py),
while adding full K=M harmonic blocks F_P^(k), F_R^(k) and upper-cut (1-u)/(1-v)/(1-t) multipliers.
"""
import argparse
import json
import math
import random
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

REPO = Path("/Users/cissie/Desktop/八电子在球面的分布/thomson-n9")
sys.path.insert(0, str(REPO / "numerics" / "bounds"))
sys.path.insert(0, str(REPO.parent / "thomson-workflow" / "certificates"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from typed_ladder import frac_dec, parse_result, PARAM_SDPA  # noqa: E402
from sdp_certify import dyad, repair_psd                     # noqa: E402
from thomson_certs.exact import is_positive_definite         # noqa: E402
from sym_cap_sdpa import (                                   # noqa: E402
    F0, F1, F2, F3, E_STAR_9 as E_STAR, S3_PERMS,
    sym_monoms_3d, canon, orbit_size, poly_mul, poly_add, poly_sym_vec,
    build_Q_polys, build_s3_isotypic_bases_exact, build_s2_vt_bases_exact,
    ceil_sqrt_rat, repair_psd_fine,
)


def monoms_3d_full(deg):
    out = []
    for s in range(deg + 1):
        for a in range(s, -1, -1):
            for b in range(s - a, -1, -1):
                out.append((a, b, s - a - b))
    return out


def monoms_s2_vt(deg):
    """Canonical (a, b, c) with b >= c and a+b+c <= deg (for v <-> t symmetry)."""
    out = []
    for s in range(deg + 1):
        for a in range(s, -1, -1):
            rem = s - a
            for b in range(rem, -1, -1):
                c = rem - b
                if b >= c:
                    out.append((a, b, c))
    return out


def monoms_s2_uv(deg):
    """Canonical (a, b, c) with a >= b and a+b+c <= deg (for u <-> v symmetry)."""
    out = []
    for s in range(deg + 1):
        for c in range(s, -1, -1):
            rem = s - c
            for a in range(rem, -1, -1):
                b = rem - a
                if a >= b:
                    out.append((a, b, c))
    return out


def build_s2_uv_bases_exact(deg):
    """Split monomials of degree <= deg under u <-> v swap into even and odd bases."""
    even, odd = [], []
    half = Fraction(1, 2)
    for s in range(deg + 1):
        for c in range(s, -1, -1):
            rem = s - c
            for a in range(rem, -1, -1):
                b = rem - a
                if a > b:
                    even.append({(a, b, c): half, (b, a, c): half})
                    odd.append({(a, b, c): half, (b, a, c): -half})
                elif a == b:
                    even.append({(a, a, c): F1})
    return even, odd


def poly_proj_vt(p, idx_vt):
    """Project polynomial p onto Sym_{v<->t}(p) canonical (a, b>=c) coordinates."""
    out = {}
    half = Fraction(1, 2)
    for (a, b, c), v in p.items():
        if not v:
            continue
        if b == c:
            idx = idx_vt[(a, b, c)]
            nv = out.get(idx, F0) + v
        else:
            key = (a, b, c) if b > c else (a, c, b)
            idx = idx_vt[key]
            nv = out.get(idx, F0) + v * half
        if nv:
            out[idx] = nv
        else:
            out.pop(idx, None)
    return out


def poly_proj_uv(p, idx_uv):
    """Project polynomial p onto Sym_{u<->v}(p) canonical (a>=b, c) coordinates."""
    out = {}
    half = Fraction(1, 2)
    for (a, b, c), v in p.items():
        if not v:
            continue
        if a == b:
            idx = idx_uv[(a, b, c)]
            nv = out.get(idx, F0) + v
        else:
            key = (a, b, c) if a > b else (b, a, c)
            idx = idx_uv[key]
            nv = out.get(idx, F0) + v * half
        if nv:
            out[idx] = nv
        else:
            out.pop(idx, None)
    return out


def eval_gm_poly(Y):
    """Given Y(u,v,t), compute gm(t) = Y(1,t,t) + Y(t,1,t) + Y(t,t,1) as dict {deg: Fraction}."""
    out = {}
    for (a, b, c), v in Y.items():
        if not v:
            continue
        for d in (b + c, a + c, a + b):
            nv = out.get(d, F0) + v
            if nv:
                out[d] = nv
            else:
                out.pop(d, None)
    return out


class SymStripModel:
    """Exact rational symmetry-reduced (2,7) pole-ring typed SDP for n=9 on u in [lo, hi], others in [lo, 1]."""

    def __init__(self, lo: Fraction, hi: Fraction, M: int, K: int,
                 include_upper_1m: bool = True,
                 lp_penalty: Fraction = Fraction(1, 10 ** 11)):
        self.n = 9
        self.lo = lo
        self.hi = hi
        self.M = M
        self.K = K
        self.include_upper_1m = include_upper_1m
        self.lp_penalty = lp_penalty
        self.D = 2 * M - 2
        self.d_H = self.D
        self.b2 = (F1 - lo) / F2
        self.c2 = (F1 - hi) / F2
        self.n_y = 2 * self.d_H + 2

        # Canonical monomial bases for the 3 slack orbits
        self.mons_A = monoms_s2_vt(self.D)
        self.idx_A = {m: i for i, m in enumerate(self.mons_A)}
        self.n_A = len(self.mons_A)

        self.mons_B = monoms_s2_uv(self.D)
        self.idx_B = {m: i for i, m in enumerate(self.mons_B)}
        self.n_B = len(self.mons_B)

        self.mons_G = sym_monoms_3d(self.D)
        self.idx_G = {m: i for i, m in enumerate(self.mons_G)}
        self.n_G = len(self.mons_G)

        # Row layout (1-based)
        self.row_A = 1
        self.row_B = self.row_A + self.n_A
        self.row_G = self.row_B + self.n_B
        self.row_mA = self.row_G + self.n_G
        self.row_mB = self.row_mA + self.n_y
        self.row_mC = self.row_mB + self.n_y
        self.row_norm = self.row_mC + self.n_y
        self.m = self.row_norm

        # LP block (block 1): e+, then +/- split for h_A, h_B, h_C, psi_Ba, psi_Cb, c_a, c_b, c_g
        d_H1 = self.d_H + 1
        pos = 1
        self.e_pos = pos
        pos += 1
        self.vpos = {}
        for name in ("h_A", "h_B", "h_C", "psi_Ba", "psi_Cb"):
            self.vpos[name] = (pos, pos + d_H1)
            pos += 2 * d_H1
        for name in ("c_a", "c_b", "c_g"):
            self.vpos[name] = (pos, pos + 1)
            pos += 2
        self.n_lp = pos - 1

        # Build PSD blocks
        self.Q = build_Q_polys(K)
        self.blocks = []

        # F_P^(k) and F_R^(k), k = 0..K-1
        for typ in ("P", "R"):
            for k in range(K):
                mk = M - k
                if mk > 0:
                    self.blocks.append(dict(name=f"F_{typ}_{k}", kind="F", typ=typ, k=k, size=mk))

        detG = {(0, 0, 0): F1, (1, 1, 1): F2, (2, 0, 0): -F1, (0, 2, 0): -F1, (0, 0, 2): -F1}
        u_lo = {(1, 0, 0): F1, (0, 0, 0): -lo}
        hi_u = {(0, 0, 0): hi, (1, 0, 0): -F1}
        v_lo = {(0, 1, 0): F1, (0, 0, 0): -lo}
        t_lo = {(0, 0, 1): F1, (0, 0, 0): -lo}
        u_hi = {(0, 0, 0): F1, (1, 0, 0): -F1}
        v_hi = {(0, 0, 0): F1, (0, 1, 0): -F1}
        t_hi = {(0, 0, 0): F1, (0, 0, 1): -F1}

        # --- Orbit A SOS (v <-> t symmetry) ---
        def add_A_s2(tag, mp, zdeg):
            if zdeg < 0:
                return
            even, odd = build_s2_vt_bases_exact(zdeg)
            if even:
                self.blocks.append(dict(name=f"SOS_A_{tag}_even", kind="sos_A", mp=mp, basis=even, size=len(even)))
            if odd:
                self.blocks.append(dict(name=f"SOS_A_{tag}_odd", kind="sos_A", mp=mp, basis=odd, size=len(odd)))

        def add_A_asym(tag, mp, zdeg):
            """Sym_{v<->t}(mp * z^T B z) for asymmetric mp like v-lo or 1-v."""
            if zdeg < 0:
                return
            mons = [{m: F1} for m in monoms_3d_full(zdeg)]
            self.blocks.append(dict(name=f"SOS_A_{tag}", kind="sos_A", mp=mp, basis=mons, size=len(mons)))

        add_A_s2("1", {(0, 0, 0): F1}, self.D // 2)
        add_A_s2("ulo", u_lo, (self.D - 1) // 2)
        add_A_s2("hiu", hi_u, (self.D - 1) // 2)
        add_A_s2("detG", detG, (self.D - 3) // 2)
        add_A_asym("vlo", v_lo, (self.D - 1) // 2)
        if include_upper_1m:
            add_A_asym("vhi", v_hi, (self.D - 1) // 2)

        # --- Orbit B SOS (u <-> v symmetry) ---
        def add_B_s2(tag, mp, zdeg):
            if zdeg < 0:
                return
            even, odd = build_s2_uv_bases_exact(zdeg)
            if even:
                self.blocks.append(dict(name=f"SOS_B_{tag}_even", kind="sos_B", mp=mp, basis=even, size=len(even)))
            if odd:
                self.blocks.append(dict(name=f"SOS_B_{tag}_odd", kind="sos_B", mp=mp, basis=odd, size=len(odd)))

        def add_B_asym(tag, mp, zdeg):
            if zdeg < 0:
                return
            mons = [{m: F1} for m in monoms_3d_full(zdeg)]
            self.blocks.append(dict(name=f"SOS_B_{tag}", kind="sos_B", mp=mp, basis=mons, size=len(mons)))

        add_B_s2("1", {(0, 0, 0): F1}, self.D // 2)
        add_B_s2("tlo", t_lo, (self.D - 1) // 2)
        add_B_s2("detG", detG, (self.D - 3) // 2)
        add_B_asym("ulo", u_lo, (self.D - 1) // 2)
        if include_upper_1m:
            add_B_s2("thi", t_hi, (self.D - 1) // 2)
            add_B_asym("uhi", u_hi, (self.D - 1) // 2)

        # --- Orbit G SOS (S3 symmetry) ---
        def add_G_s3(tag, mp, zdeg):
            if zdeg < 0:
                return
            triv, sign, std_pairs = build_s3_isotypic_bases_exact(zdeg)
            if triv:
                self.blocks.append(dict(name=f"SOS_G_{tag}_triv", kind="sos_G_plain", mp=mp, basis=triv, size=len(triv)))
            if sign:
                self.blocks.append(dict(name=f"SOS_G_{tag}_sign", kind="sos_G_plain", mp=mp, basis=sign, size=len(sign)))
            if std_pairs:
                self.blocks.append(dict(name=f"SOS_G_{tag}_std", kind="sos_G_std", mp=mp, basis=std_pairs, size=len(std_pairs)))

        def add_G_s2(tag, mp, zdeg):
            if zdeg < 0:
                return
            even, odd = build_s2_vt_bases_exact(zdeg)
            if even:
                self.blocks.append(dict(name=f"SOS_G_{tag}_even", kind="sos_G_plain", mp=mp, basis=even, size=len(even)))
            if odd:
                self.blocks.append(dict(name=f"SOS_G_{tag}_odd", kind="sos_G_plain", mp=mp, basis=odd, size=len(odd)))

        add_G_s3("1", {(0, 0, 0): F1}, self.D // 2)
        add_G_s3("detG", detG, (self.D - 3) // 2)
        add_G_s2("ulo", u_lo, (self.D - 1) // 2)
        if include_upper_1m:
            add_G_s2("uhi", u_hi, (self.D - 1) // 2)

        # --- Minorant blocks ---
        # H_A on [lo, hi]: y in [c, b], 6 blocks
        self.blocks.append(dict(name="tauA_0", kind="minor", row0=self.row_mA, pm={0: F1}, size=self.d_H + 1))
        self.blocks.append(dict(name="tauA_1", kind="minor", row0=self.row_mA, pm={1: F1}, size=self.d_H + 1))
        self.blocks.append(dict(name="tauA_2", kind="minor", row0=self.row_mA, pm={0: -self.c2, 2: F1}, size=self.d_H))
        self.blocks.append(dict(name="tauA_3", kind="minor", row0=self.row_mA, pm={0: self.b2, 2: -F1}, size=self.d_H))
        self.blocks.append(dict(name="tauA_4", kind="minor", row0=self.row_mA, pm={1: -self.c2, 3: F1}, size=self.d_H))
        self.blocks.append(dict(name="tauA_5", kind="minor", row0=self.row_mA, pm={1: self.b2, 3: -F1}, size=self.d_H))
        # H_B, H_C on [lo, 1): y in [0, b], 4 blocks each
        for cname, row0 in (("B", self.row_mB), ("C", self.row_mC)):
            self.blocks.append(dict(name=f"sig{cname}_0", kind="minor", row0=row0, pm={0: F1}, size=self.d_H + 1))
            self.blocks.append(dict(name=f"sig{cname}_1", kind="minor", row0=row0, pm={1: F1}, size=self.d_H + 1))
            self.blocks.append(dict(name=f"sig{cname}_2", kind="minor", row0=row0, pm={0: self.b2, 2: -F1}, size=self.d_H))
            self.blocks.append(dict(name=f"sig{cname}_3", kind="minor", row0=row0, pm={1: self.b2, 3: -F1}, size=self.d_H))

        self.blk_struct = [-self.n_lp] + [b["size"] for b in self.blocks]

    def _f_sym_Y(self, k, a, b):
        """Symmetrized in (a,b): (Y_k[a,b] + Y_k[b,a])/2, which is symmetric in u <-> v!"""
        Qk = self.Q[k]
        if a == b:
            return {(e0 + a, e1 + b, e2): v for (e0, e1, e2), v in Qk.items()}
        out = {}
        half = Fraction(1, 2)
        for (e0, e1, e2), v in Qk.items():
            k1 = (e0 + a, e1 + b, e2)
            k2 = (e0 + b, e1 + a, e2)
            out[k1] = out.get(k1, F0) + v * half
            out[k2] = out.get(k2, F0) + v * half
        return {kk: vv for kk, vv in out.items() if vv}

    def block_entry_map(self, blk, a, b):
        """SDPA bare-entry dict {row_1based: Fraction} for block entry (a, b) with a <= b."""
        kind = blk["kind"]
        if kind == "F":
            typ = blk["typ"]
            k = blk["k"]
            Y = self._f_sym_Y(k, a, b)  # symmetric in u <-> v!
            gm = eval_gm_poly(Y)
            res = {}

            def add_to(r, v):
                if v:
                    nv = res.get(r, F0) + v
                    if nv:
                        res[r] = nv
                    else:
                        res.pop(r, None)

            if typ == "P":
                # Contributions of s_P:
                # 1) lambda_A: -2*gm_P(u)/7 - 2*(s_P(u,v,t) + s_P(u,t,v))
                # Note Y(u,v,t) + Y(u,t,v) is 2*Sym_{v<->t}(Y(u,v,t))!
                for d, v in gm.items():
                    add_to(self.row_A + self.idx_A[(d, 0, 0)], -Fraction(2, 7) * v)
                for idx, v in poly_proj_vt(Y, self.idx_A).items():
                    add_to(self.row_A + idx, -Fraction(4) * v)  # -2 * (2 * Sym_vt(Y))

                # 2) lambda_B: -gm_P(u)/6 - gm_P(v)/6 - 2*s_P(u,v,t)
                # Note gm(u)+gm(v) projected to u>=v: coeff is 2*gm[0] at (0,0,0), gm[d] at (d,0,0) for d>0!
                # Check: Sym_{uv}(u^d) has coeff 1/2 at (d,0,0) for d>0, so u^d + v^d has coeff 1 at (d,0,0)!
                for d, v in gm.items():
                    if d == 0:
                        add_to(self.row_B + self.idx_B[(0, 0, 0)], -Fraction(2, 6) * v)
                    else:
                        add_to(self.row_B + self.idx_B[(d, 0, 0)], -Fraction(1, 6) * v)
                for idx, v in poly_proj_uv(Y, self.idx_B).items():
                    add_to(self.row_B + idx, -F2 * v)

                # 3) lambda_G: 0 (no P in RRR!)
                # 4) normalization: -2*s_P(1,1,1)
                y111 = sum(Y.values(), F0)
                if y111:
                    add_to(self.row_norm, -F2 * y111)
            else:  # typ == "R"
                # 1) lambda_A: -2*s_R(v, t, u)
                # permute (u,v,t) -> (v,t,u): exponent (e0,e1,e2) becomes (e2, e0, e1)
                Y_vtu = {(e2, e0, e1): v for (e0, e1, e2), v in Y.items()}
                for idx, v in poly_proj_vt(Y_vtu, self.idx_A).items():
                    add_to(self.row_A + idx, -F2 * v)

                # 2) lambda_B: -gm_R(u)/6 - gm_R(v)/6 - 2*(s_R(u,t,v) + s_R(v,t,u))
                for d, v in gm.items():
                    if d == 0:
                        add_to(self.row_B + self.idx_B[(0, 0, 0)], -Fraction(2, 6) * v)
                    else:
                        add_to(self.row_B + self.idx_B[(d, 0, 0)], -Fraction(1, 6) * v)
                # Y(u,t,v) + Y(v,t,u) = 2 * Sym_{u<->v}(Y(u,t,v))
                Y_utv = {(e0, e2, e1): v for (e0, e1, e2), v in Y.items()}
                for idx, v in poly_proj_uv(Y_utv, self.idx_B).items():
                    add_to(self.row_B + idx, -Fraction(4) * v)

                # 3) lambda_G: -2*(gm_R(u)+gm_R(v)+gm_R(t))/5 - 2*(s_R(u,v,t)+s_R(u,t,v)+s_R(v,t,u))
                # Note s_R(u,v,t)+s_R(u,t,v)+s_R(v,t,u) = 3 * Sym_{S3}(Y)
                for d, v in gm.items():
                    if d == 0:
                        add_to(self.row_G + self.idx_G[(0, 0, 0)], -Fraction(6, 5) * v)
                    else:
                        add_to(self.row_G + self.idx_G[(d, 0, 0)], -Fraction(2, 5) * v)
                for idx, v in poly_sym_vec(Y, self.idx_G).items():
                    add_to(self.row_G + idx, -Fraction(6) * v)

                # 4) normalization: -7*s_R(1,1,1)
                y111 = sum(Y.values(), F0)
                if y111:
                    add_to(self.row_norm, -Fraction(7) * y111)
            return res

        elif kind == "sos_A":
            B = blk["basis"]
            p = poly_mul(blk["mp"], poly_mul(B[a], B[b]))
            return {self.row_A + idx: -v for idx, v in poly_proj_vt(p, self.idx_A).items() if v}

        elif kind == "sos_B":
            B = blk["basis"]
            p = poly_mul(blk["mp"], poly_mul(B[a], B[b]))
            return {self.row_B + idx: -v for idx, v in poly_proj_uv(p, self.idx_B).items() if v}

        elif kind == "sos_G_plain":
            B = blk["basis"]
            p = poly_mul(blk["mp"], poly_mul(B[a], B[b]))
            return {self.row_G + idx: -v for idx, v in poly_sym_vec(p, self.idx_G).items() if v}

        elif kind == "sos_G_std":
            B = blk["basis"]
            p = poly_add(poly_mul(B[a][0], B[b][0]), poly_mul(B[a][1], B[b][1]), F3)
            p = {kk: vv / F3 for kk, vv in p.items()}
            pm = poly_mul(blk["mp"], p)
            return {self.row_G + idx: -v for idx, v in poly_sym_vec(pm, self.idx_G).items() if v}

        elif kind == "minor":
            pm = blk["pm"]
            row0 = blk["row0"]
            out = {}
            for dp, vp in pm.items():
                deg = a + b + dp
                if deg < self.n_y:
                    r = row0 + deg
                    out[r] = out.get(r, F0) + vp
            return {r: v for r, v in out.items() if v}

        raise ValueError(kind)

    def build_sdpa_entries(self):
        acc = {}

        def put(k, l, i, j, v):
            if v:
                nv = acc.get((k, l, i, j), F0) + v
                if nv:
                    acc[(k, l, i, j)] = nv
                else:
                    acc.pop((k, l, i, j), None)

        def put_split(r, name, d, v):
            pp, mm = self.vpos[name]
            put(r, 1, pp + d, pp + d, v)
            put(r, 1, mm + d, mm + d, -v)

        # Objective
        put(0, 1, self.e_pos, self.e_pos, F1)
        if self.lp_penalty:
            for name, (pp, mm) in self.vpos.items():
                sz = mm - pp
                for d in range(sz):
                    put(0, 1, pp + d, pp + d, -self.lp_penalty)
                    put(0, 1, mm + d, mm + d, -self.lp_penalty)

        # Normalization: 7 c_a + 42 c_b + 35 c_g - e - 2 s_P(1,1,1) - 7 s_R(1,1,1) = 0
        put(self.row_norm, 1, self.e_pos, self.e_pos, -F1)
        put_split(self.row_norm, "c_a", 0, Fraction(7))
        put_split(self.row_norm, "c_b", 0, Fraction(42))
        put_split(self.row_norm, "c_g", 0, Fraction(35))

        # Slack LP terms:
        # lambda_A: h_A(u)/7 + psi_Ba(v) + psi_Ba(t) - c_a
        put_split(self.row_A + self.idx_A[(0, 0, 0)], "c_a", 0, -F1)
        for d in range(self.d_H + 1):
            put_split(self.row_A + self.idx_A[(d, 0, 0)], "h_A", d, Fraction(1, 7))
            if d == 0:
                put_split(self.row_A + self.idx_A[(0, 0, 0)], "psi_Ba", 0, F2)
            else:
                put_split(self.row_A + self.idx_A[(0, d, 0)], "psi_Ba", d, F1)

        # lambda_B: (h_B - psi_Ba)(u)/6 + (h_B - psi_Ba)(v)/6 + psi_Cb(t) - c_b
        put_split(self.row_B + self.idx_B[(0, 0, 0)], "c_b", 0, -F1)
        for d in range(self.d_H + 1):
            if d == 0:
                put_split(self.row_B + self.idx_B[(0, 0, 0)], "h_B", 0, Fraction(2, 6))
                put_split(self.row_B + self.idx_B[(0, 0, 0)], "psi_Ba", 0, -Fraction(2, 6))
            else:
                put_split(self.row_B + self.idx_B[(d, 0, 0)], "h_B", d, Fraction(1, 6))
                put_split(self.row_B + self.idx_B[(d, 0, 0)], "psi_Ba", d, -Fraction(1, 6))
            put_split(self.row_B + self.idx_B[(0, 0, d)], "psi_Cb", d, F1)

        # lambda_G: (h_C - 2*psi_Cb)(u,v,t)/5 - c_g
        put_split(self.row_G + self.idx_G[(0, 0, 0)], "c_g", 0, -F1)
        for d in range(self.d_H + 1):
            if d == 0:
                put_split(self.row_G + self.idx_G[(0, 0, 0)], "h_C", 0, Fraction(3, 5))
                put_split(self.row_G + self.idx_G[(0, 0, 0)], "psi_Cb", 0, -Fraction(6, 5))
            else:
                put_split(self.row_G + self.idx_G[(d, 0, 0)], "h_C", d, Fraction(1, 5))
                put_split(self.row_G + self.idx_G[(d, 0, 0)], "psi_Cb", d, -Fraction(2, 5))

        # Minorant LP terms: 2y H_X(1-2y^2) + minor_SOS = 1
        for name, row0 in (("h_A", self.row_mA), ("h_B", self.row_mB), ("h_C", self.row_mC)):
            for d in range(self.d_H + 1):
                for j in range(d + 1):
                    c_yj = Fraction(2 * math.comb(d, j) * ((-2) ** j))
                    put_split(row0 + (2 * j + 1), name, d, c_yj)

        # PSD blocks
        for b_idx, blk in enumerate(self.blocks):
            l = 2 + b_idx
            sz = blk["size"]
            for a in range(sz):
                for b in range(a, sz):
                    emap = self.block_entry_map(blk, a, b)
                    for r, v in emap.items():
                        put(r, l, a + 1, b + 1, v)

        return [(k, l, i, j, v) for (k, l, i, j), v in acc.items()]

    def write_dat(self, path: Path):
        t0 = time.time()
        entries = self.build_sdpa_entries()
        b_vec = [F0] * self.m
        b_vec[self.row_mA - 1] = F1
        b_vec[self.row_mB - 1] = F1
        b_vec[self.row_mC - 1] = F1
        entries.sort(key=lambda x: (x[0], x[1], x[2], x[3]))
        lines = [
            f"{self.m}\n",
            f"{len(self.blk_struct)}\n",
            " ".join(str(x) for x in self.blk_struct) + "\n",
            " ".join(frac_dec(x) for x in b_vec) + "\n",
        ]
        for (k, l, i, j, v) in entries:
            lines.append(f"{k} {l} {i} {j} {frac_dec(v)}\n")
        path.write_text("".join(lines))
        return dict(m=self.m, n_blocks=len(self.blk_struct), n_entries=len(entries),
                    export_s=round(time.time() - t0, 2))

    def exact_residuals(self, lp_vals: dict, psd_mats: list):
        """Exact Fraction residual recomputation on all rows + exact R1_A, R1_B, R1_G, R2_A, R2_B, R2_C."""
        res = [F0] * self.m
        res[self.row_mA - 1] = -F1
        res[self.row_mB - 1] = -F1
        res[self.row_mC - 1] = -F1

        # Normalization
        res[self.row_norm - 1] += -lp_vals["e"] + 7 * lp_vals["c_a"] + 42 * lp_vals["c_b"] + 35 * lp_vals["c_g"]

        # Slack LP
        res[self.row_A - 1 + self.idx_A[(0, 0, 0)]] -= lp_vals["c_a"]
        for d in range(self.d_H + 1):
            res[self.row_A - 1 + self.idx_A[(d, 0, 0)]] += lp_vals["h_A"][d] / Fraction(7)
            if d == 0:
                res[self.row_A - 1 + self.idx_A[(0, 0, 0)]] += F2 * lp_vals["psi_Ba"][0]
            else:
                res[self.row_A - 1 + self.idx_A[(0, d, 0)]] += lp_vals["psi_Ba"][d]

        res[self.row_B - 1 + self.idx_B[(0, 0, 0)]] -= lp_vals["c_b"]
        for d in range(self.d_H + 1):
            diff = lp_vals["h_B"][d] - lp_vals["psi_Ba"][d]
            if d == 0:
                res[self.row_B - 1 + self.idx_B[(0, 0, 0)]] += diff / F3
            else:
                res[self.row_B - 1 + self.idx_B[(d, 0, 0)]] += diff / Fraction(6)
            res[self.row_B - 1 + self.idx_B[(0, 0, d)]] += lp_vals["psi_Cb"][d]

        res[self.row_G - 1 + self.idx_G[(0, 0, 0)]] -= lp_vals["c_g"]
        for d in range(self.d_H + 1):
            diff = lp_vals["h_C"][d] - F2 * lp_vals["psi_Cb"][d]
            if d == 0:
                res[self.row_G - 1 + self.idx_G[(0, 0, 0)]] += Fraction(3, 5) * diff
            else:
                res[self.row_G - 1 + self.idx_G[(d, 0, 0)]] += diff / Fraction(5)

        # Minorant LP
        for name, row0 in (("h_A", self.row_mA), ("h_B", self.row_mB), ("h_C", self.row_mC)):
            hv = lp_vals[name]
            for d in range(self.d_H + 1):
                if not hv[d]:
                    continue
                for j in range(d + 1):
                    c_yj = Fraction(2 * math.comb(d, j) * ((-2) ** j))
                    res[row0 - 1 + (2 * j + 1)] += c_yj * hv[d]

        # PSD blocks
        for blk, mat in zip(self.blocks, psd_mats):
            sz = blk["size"]
            for a in range(sz):
                for b in range(a, sz):
                    x_ab = mat[a][b]
                    if not x_ab:
                        continue
                    mult = F1 if a == b else F2
                    for r, v in self.block_entry_map(blk, a, b).items():
                        res[r - 1] += mult * x_ab * v

        # Compute exact full-monomial L1 norms (accounting for orbit sizes!)
        R1_A = F0
        for i, (a, b, c) in enumerate(self.mons_A):
            mult = 1 if b == c else 2
            R1_A += mult * abs(res[self.row_A - 1 + i])
        R1_B = F0
        for i, (a, b, c) in enumerate(self.mons_B):
            mult = 1 if a == b else 2
            R1_B += mult * abs(res[self.row_B - 1 + i])
        R1_G = F0
        for i, c in enumerate(self.mons_G):
            R1_G += orbit_size(c) * abs(res[self.row_G - 1 + i])

        w_hat = ceil_sqrt_rat(self.b2, bits=80)
        R2 = {}
        for cname, row0 in (("A", self.row_mA), ("B", self.row_mB), ("C", self.row_mC)):
            acc = F0
            wp = F1
            for j in range(self.n_y):
                acc += abs(res[row0 - 1 + j]) * wp
                wp *= w_hat
            R2[cname] = acc
        norm_err = abs(res[self.row_norm - 1])
        return dict(R1_A=R1_A, R1_B=R1_B, R1_G=R1_G, R2=R2, norm_err=norm_err)

    def certify_from_result(self, res_path: Path, k_bits: int = 64):
        parsed = parse_result(res_path)
        info = parsed["info"]
        lp = parsed["lp"]
        assert len(lp) == self.n_lp

        def get_split(name, is_poly=True):
            pp, mm = self.vpos[name]
            if is_poly:
                return [lp[pp - 1 + d] - lp[mm - 1 + d] for d in range(self.d_H + 1)]
            return lp[pp - 1] - lp[mm - 1]

        lp_raw = dict(
            e=lp[self.e_pos - 1],
            h_A=get_split("h_A"), h_B=get_split("h_B"), h_C=get_split("h_C"),
            psi_Ba=get_split("psi_Ba"), psi_Cb=get_split("psi_Cb"),
            c_a=get_split("c_a", False), c_b=get_split("c_b", False), c_g=get_split("c_g", False),
        )
        psd_raw = [[[Fraction(x) for x in row] for row in g] for g in parsed["sdp"]]
        raw_res = self.exact_residuals(lp_raw, psd_raw)

        # Dyadic rounding + exact LDL^T PSD repair
        e_d = dyad(lp_raw["e"], k_bits, floor=True)
        lp_d = dict(
            e=e_d,
            h_A=[dyad(x, k_bits) for x in lp_raw["h_A"]],
            h_B=[dyad(x, k_bits) for x in lp_raw["h_B"]],
            h_C=[dyad(x, k_bits) for x in lp_raw["h_C"]],
            psi_Ba=[dyad(x, k_bits) for x in lp_raw["psi_Ba"]],
            psi_Cb=[dyad(x, k_bits) for x in lp_raw["psi_Cb"]],
            c_a=dyad(lp_raw["c_a"], k_bits),
            c_b=dyad(lp_raw["c_b"], k_bits),
            c_g=F0,  # recomputed exactly from normalization below!
        )
        psd_d = []
        repairs = {}
        sP_111 = F0
        sR_111 = F0
        for blk, mat in zip(self.blocks, psd_raw):
            sz = blk["size"]
            M_d = [[dyad(mat[i][j], k_bits) for j in range(sz)] for i in range(sz)]
            for i in range(sz):
                for j in range(i + 1, sz):
                    M_d[j][i] = M_d[i][j]
            M_rep, delta = repair_psd_fine(M_d, k_bits)
            assert is_positive_definite(M_rep), f"Block {blk['name']} failed exact LDL^T!"
            psd_d.append(M_rep)
            if delta > 0:
                repairs[blk["name"]] = float(delta)
            if blk["kind"] == "F" and blk["k"] == 0:
                s111 = sum(M_rep[i][j] for i in range(sz) for j in range(sz))
                if blk["typ"] == "P":
                    sP_111 = s111
                else:
                    sR_111 = s111

        # Recompute c_g EXACTLY so normalization holds with norm_err == 0!
        lp_d["c_g"] = (e_d + 2 * sP_111 + 7 * sR_111 - 7 * lp_d["c_a"] - 42 * lp_d["c_b"]) / Fraction(35)
        d_res = self.exact_residuals(lp_d, psd_d)
        assert d_res["norm_err"] == 0, f"Normalization error nonzero: {d_res['norm_err']}"
        defl = 7 * d_res["R1_A"] + 42 * d_res["R1_B"] + 35 * d_res["R1_G"]
        R2max = max(d_res["R2"].values())
        certified = (e_d - defl) / (F1 + R2max)
        return dict(
            phase=info["phase_value"], iteration=info["iteration"],
            mu=info["mu"], relgap=info["relative_gap"],
            e_raw=float(lp_raw["e"]),
            R1_raw=float(max(raw_res["R1_A"], raw_res["R1_B"], raw_res["R1_G"])),
            R2_raw=float(max(raw_res["R2"].values())),
            norm_err_raw=float(raw_res["norm_err"]),
            k_bits=k_bits,
            R1_A=float(d_res["R1_A"]), R1_B=float(d_res["R1_B"]), R1_G=float(d_res["R1_G"]),
            R2_max=float(R2max),
            certified_exact=f"{certified.numerator}/{certified.denominator}",
            certified_float=float(certified),
            margin_vs_E_star=float(certified - E_STAR),
            repairs=repairs,
        )


def selftest():
    """Exact combinatorial identity test: verify sum_{i<j} H_cls - e == sum_T lam_T + sum_all s on random rational config!"""
    print("Running exact Fraction combinatorial identity selftest for SymStripModel (M=4, K=4)...")
    model = SymStripModel(Fraction(-79, 100), Fraction(-153, 200), M=4, K=4)
    rng = random.Random(20261120)
    # Generate random symmetric Gram matrix with 1s on diagonal
    G = [[F1 if i == j else F0 for j in range(9)] for i in range(9)]
    for i in range(9):
        for j in range(i + 1, 9):
            G[i][j] = G[j][i] = Fraction(rng.randint(-5, 5), 8)
    # Random LP polynomials & F_P, F_R
    d1 = model.d_H + 1
    rpoly = lambda: [Fraction(rng.randint(-3, 3), 4) for _ in range(d1)]
    lp = dict(e=Fraction(10), h_A=rpoly(), h_B=rpoly(), h_C=rpoly(),
              psi_Ba=rpoly(), psi_Cb=rpoly(), c_a=Fraction(1, 3), c_b=Fraction(-1, 5), c_g=F0)
    psd = []
    sP111, sR111 = F0, F0
    F_mats = {"P": {}, "R": {}}
    for blk in model.blocks:
        sz = blk["size"]
        if blk["kind"] == "F":
            M = [[Fraction(rng.randint(-2, 2), 4) for _ in range(sz)] for _ in range(sz)]
            M = [[(M[i][j] + M[j][i]) / F2 for j in range(sz)] for i in range(sz)]
            psd.append(M)
            F_mats[blk["typ"]][blk["k"]] = M
            if blk["k"] == 0:
                s = sum(M[i][j] for i in range(sz) for j in range(sz))
                if blk["typ"] == "P": sP111 = s
                else: sR111 = s
        else:
            psd.append([[F0] * sz for _ in range(sz)])
    lp["c_g"] = (lp["e"] + 2 * sP111 + 7 * sR111 - 7 * lp["c_a"] - 42 * lp["c_b"]) / Fraction(35)

    # Extract exact lambda_A, lambda_B, lambda_G polynomials via exact_residuals (with SOS=0!)
    # Wait: compute res directly using same logic, then evaluate on all 84 triples of G!
    # Recompute res vector
    res = [F0] * model.m
    res[model.row_A - 1 + model.idx_A[(0, 0, 0)]] -= lp["c_a"]
    for d in range(d1):
        res[model.row_A - 1 + model.idx_A[(d, 0, 0)]] += lp["h_A"][d] / Fraction(7)
        if d == 0: res[model.row_A - 1 + model.idx_A[(0, 0, 0)]] += F2 * lp["psi_Ba"][0]
        else: res[model.row_A - 1 + model.idx_A[(0, d, 0)]] += lp["psi_Ba"][d]
    res[model.row_B - 1 + model.idx_B[(0, 0, 0)]] -= lp["c_b"]
    for d in range(d1):
        diff = lp["h_B"][d] - lp["psi_Ba"][d]
        if d == 0: res[model.row_B - 1 + model.idx_B[(0, 0, 0)]] += diff / F3
        else: res[model.row_B - 1 + model.idx_B[(d, 0, 0)]] += diff / Fraction(6)
        res[model.row_B - 1 + model.idx_B[(0, 0, d)]] += lp["psi_Cb"][d]
    res[model.row_G - 1 + model.idx_G[(0, 0, 0)]] -= lp["c_g"]
    for d in range(d1):
        diff = lp["h_C"][d] - F2 * lp["psi_Cb"][d]
        if d == 0: res[model.row_G - 1 + model.idx_G[(0, 0, 0)]] += Fraction(3, 5) * diff
        else: res[model.row_G - 1 + model.idx_G[(d, 0, 0)]] += diff / Fraction(5)
    for blk, mat in zip(model.blocks, psd):
        if blk["kind"] != "F": continue
        sz = blk["size"]
        for a in range(sz):
            for b in range(a, sz):
                mult = F1 if a == b else F2
                for r, v in model.block_entry_map(blk, a, b).items():
                    if r < model.row_mA:
                        res[r - 1] += mult * mat[a][b] * v

    def ev_A(u, v, t):
        tot = F0
        for i, (a, b, c) in enumerate(model.mons_A):
            val = res[model.row_A - 1 + i]
            if not val: continue
            if b == c: tot += val * (u ** a) * (v ** b) * (t ** c)
            else: tot += val * (u ** a) * ((v ** b) * (t ** c) + (v ** c) * (t ** b))
        return tot

    def ev_B(u, v, t):
        tot = F0
        for i, (a, b, c) in enumerate(model.mons_B):
            val = res[model.row_B - 1 + i]
            if not val: continue
            if a == b: tot += val * (u ** a) * (v ** b) * (t ** c)
            else: tot += val * ((u ** a) * (v ** b) + (u ** b) * (v ** a)) * (t ** c)
        return tot

    def ev_G(u, v, t):
        tot = F0
        for i, c in enumerate(model.mons_G):
            val = res[model.row_G - 1 + i]
            if not val: continue
            orb = set((c[p[0]], c[p[1]], c[p[2]]) for p in S3_PERMS)
            tot += val * sum((u ** a) * (v ** b) * (t ** d) for a, b, d in orb)
        return tot

    def ev1(coeffs, x):
        return sum(c * (x ** d) for d, c in enumerate(coeffs))

    def ev_s(typ, u, v, t):
        tot = F0
        for k, M in F_mats[typ].items():
            Qk = model.Q[k]
            qv = sum(val * (u ** e0) * (v ** e1) * (t ** e2) for (e0, e1, e2), val in Qk.items())
            sz = len(M)
            for a in range(sz):
                for b in range(sz):
                    tot += M[a][b] * (u ** a) * (v ** b) * qv
        return tot

    # LHS = sum_{i<j} H_cls(G_ij) - e
    lhs = -lp["e"]
    for i in range(9):
        for j in range(i + 1, 9):
            if i < 2 and j < 2: lhs += ev1(lp["h_A"], G[i][j])
            elif i < 2: lhs += ev1(lp["h_B"], G[i][j])
            else: lhs += ev1(lp["h_C"], G[i][j])

    # RHS = sum_{unordered triples} lam_T + sum_{all ordered i,j,l} s_{type(i)}(G_ij, G_il, G_jl)
    sum_lam = F0
    for r in range(2, 9):
        sum_lam += ev_A(G[0][1], G[0][r], G[1][r])
    for p in range(2):
        for r1 in range(2, 9):
            for r2 in range(r1 + 1, 9):
                sum_lam += ev_B(G[p][r1], G[p][r2], G[r1][r2])
    for r1 in range(2, 9):
        for r2 in range(r1 + 1, 9):
            for r3 in range(r2 + 1, 9):
                sum_lam += ev_G(G[r1][r2], G[r1][r3], G[r2][r3])
    sum_all = F0
    for i in range(9):
        typ = "P" if i < 2 else "R"
        for j in range(9):
            for l in range(9):
                sum_all += ev_s(typ, G[i][j], G[i][l], G[j][l])

    assert lhs == sum_lam + sum_all, f"IDENTITY MISMATCH: LHS={lhs} vs RHS={sum_lam + sum_all}"
    print(f"  [OK] Exact rational (2,7) combinatorial identity holds with ZERO error! (LHS=RHS={float(lhs):.6f})")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--lo", type=str, default="-153/200")
    ap.add_argument("--hi", type=str, default="-187/250")
    ap.add_argument("--M", type=int, default=9)
    ap.add_argument("--K", type=int, default=9)
    ap.add_argument("--no-upper-1m", action="store_true")
    ap.add_argument("--sdpa-bin", type=str, default="/tmp/hpbuild/sdpa-gmp-7.1.3/sdpa_gmp")
    ap.add_argument("--workdir", type=str, default="/tmp/sym_strip_work")
    ap.add_argument("--tag", type=str, default=None)
    ap.add_argument("--k-bits", type=int, default=64)
    ap.add_argument("--skip-solve", action="store_true")
    args = ap.parse_args()

    if args.selftest:
        selftest()
        return

    lo, hi = Fraction(args.lo), Fraction(args.hi)
    tag = args.tag or f"strip_{str(lo).replace('/','o').replace('-','m')}_{str(hi).replace('/','o').replace('-','m')}_M{args.M}_K{args.K}"
    wdir = Path(args.workdir) / tag
    wdir.mkdir(parents=True, exist_ok=True)
    dat_path = wdir / f"{tag}.dat-s"
    res_path = wdir / f"{tag}.result"
    param_path = wdir / "param.sdpa"
    param_path.write_text(PARAM_SDPA)

    model = SymStripModel(lo, hi, args.M, args.K, include_upper_1m=not args.no_upper_1m)
    if args.skip_solve and res_path.exists():
        info = dict(m=model.m, n_blocks=len(model.blk_struct), skipped=True)
        solve_s = 0.0
    else:
        print(f"[{tag}] Building exact Fraction .dat-s (m={model.m}, A={model.n_A}, B={model.n_B}, G={model.n_G}, blks={len(model.blk_struct)}, maxBlk={max(model.blk_struct)})...", flush=True)
        info = model.write_dat(dat_path)
        print(f"[{tag}] Exported in {info['export_s']}s: entries={info['n_entries']}", flush=True)

        t0 = time.time()
        cmd = [args.sdpa_bin, "-ds", str(dat_path), "-o", str(res_path), "-p", str(param_path)]
        print(f"[{tag}] Running SDPA-GMP: {' '.join(cmd)}", flush=True)
        proc = subprocess.run(cmd, capture_output=True, text=True)
        solve_s = time.time() - t0
        if proc.returncode != 0:
            print(f"[{tag}] SDPA-GMP FAILED (exit {proc.returncode}):\n{proc.stderr[-1000:]}")
            sys.exit(1)
        print(f"[{tag}] SDPA-GMP finished in {solve_s:.1f}s. Certifying in exact Fraction...", flush=True)

    cert = model.certify_from_result(res_path, k_bits=args.k_bits)
    cert["solve_s"] = round(solve_s, 2)
    cert["export"] = info
    (wdir / f"{tag}_summary.json").write_text(json.dumps(cert, indent=2, ensure_ascii=False))
    print(f"[{tag}] RESULT: phase={cert['phase']} iter={cert['iteration']} solve_s={solve_s:.1f}s")
    print(f"  e_raw     = {cert['e_raw']:.12f}  (R1_raw={cert['R1_raw']:.2e}, R2_raw={cert['R2_raw']:.2e})")
    print(f"  certified = {cert['certified_float']:.12f}  (margin_vs_E*={cert['margin_vs_E_star']:+.4e}, R2={cert['R2_max']:.2e})", flush=True)


if __name__ == "__main__":
    main()
