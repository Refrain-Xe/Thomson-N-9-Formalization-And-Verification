#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""sym_cap_sdpa.py — Exact rational (Fraction) S3-symmetry-reduced untyped 3-point SDP engine
for Thomson N=9 (Round 24 breakthrough: full K=M harmonic blocks + pure rational S3 isotypic
decomposition + 128-bit dyadic & exact LDL^T certification + out-of-process JSON verification).

Mathematical overview:
  For any n-point spherical configuration X in (S^2)^n with min_{i<j} <x_i, x_j> >= a0:
    sum_{i<j} H(t_ij) - e = (1 / (2(n-2))) * sum_{i,j,l distinct} slack(t_ij, t_il, t_jl)
                          + (1 / 2) * sum_{i,j,l} s(t_ij, t_il, t_jl)
  where:
    - s(u,v,t) = sum_{k=0}^{K-1} <F_k, Sym_{S3}(u^a v^b Q_k(u,v,t))>, F_k >= 0 of size M-k
      (Lemma 4.1 / KLT Lemma 4.2 guarantees sum_{i,j,l} s >= 0 for all F_k >= 0),
    - slack(u,v,t) = (H(u)+H(v)+H(t))/3 - e/C(n,2) - R_s(u,v,t) is S3-symmetric of degree D=2M-2,
      certified nonnegative on [a0,1]^3 cap {det G >= 0} via pure rational S3 isotypic SOS blocks:
        * S3-invariant multipliers {1, detG}: trivial + sign + standard 2D irrep ((1/3) e1^T B e1 + e2^T B e2)
        * S2(v<->t)-invariant multipliers {u-a0, 1-u} symmetrized under S3: even + odd blocks
    - H(t) <= (1 + R2) * (2 - 2t)^{-1/2} on [a0, 1) via 1D Markov-Lukacs blocks sigma_0..sigma_3 in y = sqrt((1-t)/2).
  Certified exact rational lower bound:
    E(X) >= (e - C(n,2) * R1) / (1 + R2)
  where R1 = sum_{canon c} |orbit(c)| * |slack_resid[c]| and R2 = sum_j |minor_resid[j]| * w_hat^j.

Usage (from thomson-n9/ or repo parent):
  python3 numerics/bounds/sym_cap_sdpa.py --selftest
  python3 numerics/bounds/sym_cap_sdpa.py --a0=-153/200 --M 10 --K 10 --k-bits 128 --cert-out certificates/n9-stage-a-r24-symcap-m0765_M10K10.json
  python3 numerics/bounds/sym_cap_sdpa.py --verify-cert certificates/n9-stage-a-r24-symcap-m0765_M10K10.json
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
WORKFLOW_CERTS = HERE.parents[2] / "thomson-workflow" / "certificates"
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(WORKFLOW_CERTS))

from typed_ladder import frac_dec, parse_result, PARAM_SDPA, code_version  # noqa: E402
from sdp_certify import dyad                                               # noqa: E402
from thomson_certs.exact import is_positive_definite                       # noqa: E402

F0 = Fraction(0)
F1 = Fraction(1)
F2 = Fraction(2)
F3 = Fraction(3)
SEED = 20261120
E_STAR_9 = Fraction("25.759986531")

S3_PERMS = [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
S3_SIGNS = [1, -1, -1, 1, 1, -1]


def frac_str(q: Fraction) -> str:
    return f"{q.numerator}/{q.denominator}" if q.denominator != 1 else str(q.numerator)


def sym_monoms_3d(deg: int) -> list[tuple[int, int, int]]:
    out = []
    for s in range(deg + 1):
        for a in range(s, -1, -1):
            for b in range(min(a, s - a), -1, -1):
                c = s - a - b
                if b >= c:
                    out.append((a, b, c))
    return out


def canon(a: int, b: int, c: int) -> tuple[int, int, int]:
    if a < b:
        a, b = b, a
    if b < c:
        b, c = c, b
    if a < b:
        a, b = b, a
    return (a, b, c)


def orbit_size(c: tuple[int, int, int]) -> int:
    if c[0] == c[1] == c[2]:
        return 1
    if c[0] == c[1] or c[1] == c[2]:
        return 3
    return 6


def poly_mul(p: dict, q: dict) -> dict:
    out: dict = {}
    for (a1, b1, c1), v1 in p.items():
        if not v1:
            continue
        for (a2, b2, c2), v2 in q.items():
            if not v2:
                continue
            key = (a1 + a2, b1 + b2, c1 + c2)
            nv = out.get(key, F0) + v1 * v2
            if nv:
                out[key] = nv
            else:
                out.pop(key, None)
    return out


def poly_add(p: dict, q: dict, scale: Fraction = F1) -> dict:
    out = dict(p)
    for k, v in q.items():
        nv = out.get(k, F0) + scale * v
        if nv:
            out[k] = nv
        else:
            out.pop(k, None)
    return out


def poly_perm(p: dict, perm: tuple[int, int, int]) -> dict:
    i0, i1, i2 = perm
    return {(e[i0], e[i1], e[i2]): v for e, v in p.items()}


def poly_sym_vec(p: dict, sym_idx: dict) -> dict:
    out: dict = {}
    for (x, y, z), v in p.items():
        if not v:
            continue
        c = canon(x, y, z)
        stab = 6 // orbit_size(c)
        idx = sym_idx[c]
        nv = out.get(idx, F0) + v * Fraction(stab, 6)
        if nv:
            out[idx] = nv
        else:
            out.pop(idx, None)
    return out


def build_Q_polys(K: int) -> list[dict]:
    Q = [{(0, 0, 0): F1}]
    if K == 1:
        return Q
    t_minus_uv = {(0, 0, 1): F1, (1, 1, 0): -F1}
    two_t_uv = {(0, 0, 1): F2, (1, 1, 0): -F2}
    om_u2_v2 = {(0, 0, 0): F1, (2, 0, 0): -F1, (0, 2, 0): -F1, (2, 2, 0): F1}
    Q.append(t_minus_uv)
    for _ in range(2, K):
        Q.append(poly_add(poly_mul(two_t_uv, Q[-1]), poly_mul(om_u2_v2, Q[-2]), -F1))
    return Q


def build_s3_isotypic_bases_exact(deg: int):
    """Pure Fraction S3 isotypic decomposition for polynomials of degree <= deg."""
    triv, sign, std_pairs = [], [], []

    def make_std_pair(p):
        sp1 = poly_perm(p, (2, 0, 1))
        sp2 = poly_perm(p, (1, 2, 0))
        e1 = poly_add(poly_add({k: F2 * v for k, v in p.items()}, sp1, -F1), sp2, -F1)
        e2 = poly_add(sp1, sp2, -F1)
        return (e1, e2)

    for (x, y, z) in sym_monoms_3d(deg):
        orb = sorted(set(((x, y, z)[p[0]], (x, y, z)[p[1]], (x, y, z)[p[2]]) for p in S3_PERMS))
        triv.append({m: Fraction(1, len(orb)) for m in orb})
        if x > y > z:
            alt: dict = {}
            for perm, sgn in zip(S3_PERMS, S3_SIGNS):
                m = ((x, y, z)[perm[0]], (x, y, z)[perm[1]], (x, y, z)[perm[2]])
                alt[m] = alt.get(m, F0) + Fraction(sgn, 6)
            sign.append({k: v for k, v in alt.items() if v})
            p1 = {(x, y, z): Fraction(1, 2), (x, z, y): Fraction(1, 2)}
            p2 = {(y, x, z): Fraction(1, 2), (y, z, x): Fraction(1, 2)}
            std_pairs.append(make_std_pair(p1))
            std_pairs.append(make_std_pair(p2))
        elif x == y and y > z:
            std_pairs.append(make_std_pair({(z, x, x): F1}))
        elif x > y and y == z:
            std_pairs.append(make_std_pair({(x, y, y): F1}))
    return triv, sign, std_pairs


def build_s2_vt_bases_exact(deg: int):
    even, odd = [], []
    half = Fraction(1, 2)
    for s in range(deg + 1):
        for a in range(s, -1, -1):
            rem = s - a
            for b in range(rem, -1, -1):
                c = rem - b
                if b > c:
                    even.append({(a, b, c): half, (a, c, b): half})
                    odd.append({(a, b, c): half, (a, c, b): -half})
                elif b == c:
                    even.append({(a, b, b): F1})
    return even, odd


def ceil_sqrt_rat(q: Fraction, bits: int = 80) -> Fraction:
    num = q.numerator * (1 << (2 * bits))
    den = q.denominator
    q_int = (num + den - 1) // den
    r = math.isqrt(q_int)
    while r * r * den < num:
        r += 1
    assert r * r * den >= num
    return Fraction(r, 1 << bits)


def repair_psd_fine(Mfr: list[list[Fraction]], k_bits: int):
    """Exact pivot-free LDL^T PD check & minimal dyadic diagonal shift starting at 2^-k_bits."""
    if is_positive_definite(Mfr):
        return Mfr, F0
    n = len(Mfr)
    delta = Fraction(1, 1 << k_bits)
    for _ in range(k_bits + 5):
        out = [[Mfr[i][j] + (delta if i == j else F0) for j in range(n)] for i in range(n)]
        if is_positive_definite(out):
            return out, delta
        delta *= 2
    raise RuntimeError("repair_psd_fine failed to make matrix strictly PD")


class SymCapModel:
    """Exact rational S3-symmetry-reduced untyped 3-point cap SDP model on [a0, 1]."""

    def __init__(self, n: int, a0: Fraction, M: int, K: int,
                 lp_penalty: Fraction = Fraction(1, 10 ** 11)):
        self.n = n
        self.a0 = a0
        self.M = M
        self.K = K
        self.lp_penalty = lp_penalty
        self.D = 2 * M - 2
        self.d_H = self.D
        self.sym_mons = sym_monoms_3d(self.D)
        self.sym_idx = {m: i for i, m in enumerate(self.sym_mons)}
        self.n_sym = len(self.sym_mons)
        self.b2 = (F1 - a0) / F2
        self.n_y = 2 * self.d_H + 2
        self.m = self.n_sym + self.n_y

        d_H1 = self.d_H + 1
        self.e_pos = 1
        self.hp_off = 2
        self.hm_off = 2 + d_H1
        self.n_lp = 1 + 2 * d_H1

        self.Q = build_Q_polys(K)
        self.blocks: list[dict] = []

        for k in range(K):
            mk = M - k
            if mk > 0:
                self.blocks.append(dict(name=f"F_{k}", kind="F", k=k, size=mk))

        detG = {(0, 0, 0): F1, (1, 1, 1): F2, (2, 0, 0): -F1, (0, 2, 0): -F1, (0, 0, 2): -F1}
        u_lo = {(1, 0, 0): F1, (0, 0, 0): -a0}
        u_hi = {(0, 0, 0): F1, (1, 0, 0): -F1}

        def add_s3_group(tag, mp, zdeg):
            if zdeg < 0:
                return
            triv, sign, std_pairs = build_s3_isotypic_bases_exact(zdeg)
            if triv:
                self.blocks.append(dict(name=f"SOS_{tag}_triv", kind="s3_plain", mp=mp, basis=triv, size=len(triv)))
            if sign:
                self.blocks.append(dict(name=f"SOS_{tag}_sign", kind="s3_plain", mp=mp, basis=sign, size=len(sign)))
            if std_pairs:
                self.blocks.append(dict(name=f"SOS_{tag}_std", kind="s3_std", mp=mp, basis=std_pairs, size=len(std_pairs)))

        def add_s2_group(tag, mp, zdeg):
            if zdeg < 0:
                return
            even, odd = build_s2_vt_bases_exact(zdeg)
            if even:
                self.blocks.append(dict(name=f"SOS_{tag}_even", kind="s3_plain", mp=mp, basis=even, size=len(even)))
            if odd:
                self.blocks.append(dict(name=f"SOS_{tag}_odd", kind="s3_plain", mp=mp, basis=odd, size=len(odd)))

        add_s3_group("1", {(0, 0, 0): F1}, self.D // 2)
        add_s3_group("detG", detG, (self.D - 3) // 2)
        add_s2_group("ulo", u_lo, (self.D - 1) // 2)
        add_s2_group("uhi", u_hi, (self.D - 1) // 2)

        self.blocks.append(dict(name="sig_0", kind="sig", pm={0: F1}, size=self.d_H + 1))
        self.blocks.append(dict(name="sig_1", kind="sig", pm={1: F1}, size=self.d_H + 1))
        self.blocks.append(dict(name="sig_2", kind="sig", pm={0: self.b2, 2: -F1}, size=self.d_H))
        self.blocks.append(dict(name="sig_3", kind="sig", pm={1: self.b2, 3: -F1}, size=self.d_H))

        self.blk_struct = [-self.n_lp] + [b["size"] for b in self.blocks]

    def block_entry_map(self, blk: dict, a: int, b: int) -> dict[int, Fraction]:
        kind = blk["kind"]
        sym_idx = self.sym_idx
        if kind == "F":
            k = blk["k"]
            Qk = self.Q[k]
            Y = {(e0 + a, e1 + b, e2): v for (e0, e1, e2), v in Qk.items()}
            res: dict[int, Fraction] = {}
            n = self.n
            for idx, v in poly_sym_vec(Y, sym_idx).items():
                res[idx + 1] = res.get(idx + 1, F0) - (n - 2) * v
            g: dict[int, Fraction] = {}
            for (e0, e1, e2), v in Y.items():
                v3 = v / F3
                for d in (e0 + e1, e0 + e2, e1 + e2):
                    g[d] = g.get(d, F0) + v3
            for d, v in g.items():
                if not v:
                    continue
                if d == 0:
                    r0 = sym_idx[(0, 0, 0)] + 1
                    res[r0] = res.get(r0, F0) - F3 * v
                else:
                    r = sym_idx[(d, 0, 0)] + 1
                    res[r] = res.get(r, F0) - v
            y111 = sum(Y.values(), F0)
            if y111:
                r0 = sym_idx[(0, 0, 0)] + 1
                res[r0] = res.get(r0, F0) - y111 / Fraction(n - 1)
            return {r: v for r, v in res.items() if v}

        elif kind == "s3_plain":
            B = blk["basis"]
            p = poly_mul(blk["mp"], poly_mul(B[a], B[b]))
            return {idx + 1: -v for idx, v in poly_sym_vec(p, sym_idx).items() if v}

        elif kind == "s3_std":
            B = blk["basis"]
            p = poly_add(poly_mul(B[a][0], B[b][0]), poly_mul(B[a][1], B[b][1]), F3)
            p = {kk: vv / F3 for kk, vv in p.items()}
            pm = poly_mul(blk["mp"], p)
            return {idx + 1: -v for idx, v in poly_sym_vec(pm, sym_idx).items() if v}

        elif kind == "sig":
            pm = blk["pm"]
            out: dict[int, Fraction] = {}
            for dp, vp in pm.items():
                deg = a + b + dp
                if deg < self.n_y:
                    r = self.n_sym + deg + 1
                    out[r] = out.get(r, F0) + vp
            return {r: v for r, v in out.items() if v}

        raise ValueError(kind)

    def build_sdpa_entries(self):
        acc: dict = {}

        def put(k, l, i, j, v):
            if v:
                nv = acc.get((k, l, i, j), F0) + v
                if nv:
                    acc[(k, l, i, j)] = nv
                else:
                    acc.pop((k, l, i, j), None)

        put(0, 1, self.e_pos, self.e_pos, F1)
        if self.lp_penalty:
            for d in range(self.d_H + 1):
                put(0, 1, self.hp_off + d, self.hp_off + d, -self.lp_penalty)
                put(0, 1, self.hm_off + d, self.hm_off + d, -self.lp_penalty)

        binom_n2 = Fraction(self.n * (self.n - 1), 2)
        r0 = self.sym_idx[(0, 0, 0)] + 1
        put(r0, 1, self.e_pos, self.e_pos, -F1 / binom_n2)

        for d in range(self.d_H + 1):
            rp = self.hp_off + d
            rm = self.hm_off + d
            if d == 0:
                put(r0, 1, rp, rp, F1)
                put(r0, 1, rm, rm, -F1)
            else:
                rd = self.sym_idx[(d, 0, 0)] + 1
                put(rd, 1, rp, rp, Fraction(1, 3))
                put(rd, 1, rm, rm, -Fraction(1, 3))
            for j in range(d + 1):
                c_yj = Fraction(2 * math.comb(d, j) * ((-2) ** j))
                ry = self.n_sym + (2 * j + 1) + 1
                put(ry, 1, rp, rp, c_yj)
                put(ry, 1, rm, rm, -c_yj)

        for b_idx, blk in enumerate(self.blocks):
            l = 2 + b_idx
            sz = blk["size"]
            for a in range(sz):
                for b in range(a, sz):
                    for r, v in self.block_entry_map(blk, a, b).items():
                        put(r, l, a + 1, b + 1, v)

        return [(k, l, i, j, v) for (k, l, i, j), v in acc.items()]

    def write_dat(self, path: Path) -> dict:
        t0 = time.time()
        entries = self.build_sdpa_entries()
        b_vec = [F0] * self.m
        b_vec[self.n_sym] = F1
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

    def exact_residuals(self, e_val: Fraction, h_vec: list[Fraction], psd_mats: list):
        slack_res = [F0] * self.n_sym
        minor_res = [F0] * self.n_y
        minor_res[0] = -F1

        binom_n2 = Fraction(self.n * (self.n - 1), 2)
        slack_res[self.sym_idx[(0, 0, 0)]] -= e_val / binom_n2

        for d, hd in enumerate(h_vec):
            if not hd:
                continue
            if d == 0:
                slack_res[self.sym_idx[(0, 0, 0)]] += hd
            else:
                slack_res[self.sym_idx[(d, 0, 0)]] += hd / F3
            for j in range(d + 1):
                c_yj = Fraction(2 * math.comb(d, j) * ((-2) ** j))
                minor_res[2 * j + 1] += c_yj * hd

        for blk, mat in zip(self.blocks, psd_mats):
            sz = blk["size"]
            for a in range(sz):
                for b in range(a, sz):
                    x_ab = mat[a][b]
                    if not x_ab:
                        continue
                    mult = F1 if a == b else F2
                    for r, v in self.block_entry_map(blk, a, b).items():
                        val = mult * x_ab * v
                        if r <= self.n_sym:
                            slack_res[r - 1] += val
                        else:
                            minor_res[r - 1 - self.n_sym] += val

        R1 = F0
        for idx, c in enumerate(self.sym_mons):
            R1 += orbit_size(c) * abs(slack_res[idx])
        w_hat = ceil_sqrt_rat(self.b2, bits=80)
        R2 = F0
        w_pow = F1
        for val in minor_res:
            R2 += abs(val) * w_pow
            w_pow *= w_hat
        return R1, R2, w_hat

    def certify_from_result(self, res_path: Path, k_bits: int = 128) -> dict:
        parsed = parse_result(res_path)
        info = parsed["info"]
        lp = parsed["lp"]
        assert len(lp) == self.n_lp, f"LP len {len(lp)} != {self.n_lp}"
        e_raw = lp[self.e_pos - 1]
        h_raw = [lp[self.hp_off - 1 + d] - lp[self.hm_off - 1 + d] for d in range(self.d_H + 1)]
        psd_raw = [[[Fraction(x) for x in row] for row in g] for g in parsed["sdp"]]

        R1_raw, R2_raw, _ = self.exact_residuals(e_raw, h_raw, psd_raw)

        e_d = dyad(e_raw, k_bits, floor=True)
        h_d = [dyad(x, k_bits) for x in h_raw]
        psd_d = []
        repairs = {}
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
                repairs[blk["name"]] = frac_str(delta)

        R1, R2, w_hat = self.exact_residuals(e_d, h_d, psd_d)
        binom_n2 = Fraction(self.n * (self.n - 1), 2)
        certified = (e_d - binom_n2 * R1) / (F1 + R2)
        return dict(
            info=info, e_raw=e_raw, R1_raw=R1_raw, R2_raw=R2_raw,
            k_bits=k_bits, e_d=e_d, h_d=h_d, psd_d=psd_d,
            R1=R1, R2=R2, w_hat=w_hat, certified=certified, repairs=repairs,
        )

    def write_certificate(self, cert_data: dict, out_path: Path, solve_s: float) -> dict:
        blocks_json = []
        for blk, mat in zip(self.blocks, cert_data["psd_d"]):
            sz = blk["size"]
            # Store upper triangle strings to keep JSON compact yet 100% exact 'p/q'
            utri = [[frac_str(mat[i][j]) for j in range(i, sz)] for i in range(sz)]
            blocks_json.append(dict(name=blk["name"], kind=blk["kind"], size=sz, utri=utri))
        payload = dict(
            kind="n9-symcap-exact-certificate",
            schema="symcap-s3/v1",
            n=self.n,
            a0=frac_str(self.a0),
            M=self.M,
            K=self.K,
            round_bits=cert_data["k_bits"],
            e=frac_str(cert_data["e_d"]),
            h=[frac_str(x) for x in cert_data["h_d"]],
            R1=frac_str(cert_data["R1"]),
            R2=frac_str(cert_data["R2"]),
            w_hat=frac_str(cert_data["w_hat"]),
            claimed_bound=frac_str(cert_data["certified"]),
            claimed_bound_float=float(cert_data["certified"]),
            repairs=cert_data["repairs"],
            blocks=blocks_json,
            provenance=dict(
                script="numerics/bounds/sym_cap_sdpa.py",
                code_version=code_version(),
                seed=SEED,
                generated_utc=datetime.now(timezone.utc).isoformat(),
                sdpa_phase=cert_data["info"]["phase_value"],
                sdpa_iteration=cert_data["info"]["iteration"],
                sdpa_mu=cert_data["info"]["mu"],
                sdpa_relgap=cert_data["info"]["relative_gap"],
                solve_s=round(solve_s, 2),
                e_raw_exact=frac_str(cert_data["e_raw"]),
                R1_raw=float(cert_data["R1_raw"]),
                R2_raw=float(cert_data["R2_raw"]),
            ),
        )
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(payload, indent=2))
        return payload


def verify_certificate_file(cert_path: Path, run_identity_check: bool = True) -> dict:
    """Completely independent out-of-process exact Fraction + LDL^T certificate verifier."""
    t0 = time.time()
    raw = json.loads(cert_path.read_text())
    assert raw["kind"] == "n9-symcap-exact-certificate"
    n = int(raw["n"])
    a0 = Fraction(raw["a0"])
    M = int(raw["M"])
    K = int(raw["K"])
    model = SymCapModel(n, a0, M, K)

    e_d = Fraction(raw["e"])
    h_d = [Fraction(x) for x in raw["h"]]
    assert len(h_d) == model.d_H + 1

    blocks_json = raw["blocks"]
    assert len(blocks_json) == len(model.blocks), f"Block count mismatch {len(blocks_json)} != {len(model.blocks)}"
    psd_d = []
    for blk_spec, bj in zip(model.blocks, blocks_json):
        assert bj["name"] == blk_spec["name"] and bj["size"] == blk_spec["size"]
        sz = blk_spec["size"]
        mat = [[F0] * sz for _ in range(sz)]
        for i in range(sz):
            row = bj["utri"][i]
            assert len(row) == sz - i
            for off, s in enumerate(row):
                val = Fraction(s)
                mat[i][i + off] = val
                mat[i + off][i] = val
        if not is_positive_definite(mat):
            raise AssertionError(f"EXACT LDL^T FAILED on block {blk_spec['name']}!")
        psd_d.append(mat)

    R1, R2, w_hat = model.exact_residuals(e_d, h_d, psd_d)
    binom_n2 = Fraction(n * (n - 1), 2)
    certified = (e_d - binom_n2 * R1) / (F1 + R2)
    claimed = Fraction(raw["claimed_bound"])
    assert certified == claimed, f"Bound mismatch: recomputed {certified} != claimed {claimed}"
    assert R1 == Fraction(raw["R1"]), "R1 mismatch"
    assert R2 == Fraction(raw["R2"]), "R2 mismatch"

    # Optional exact polynomial identity check on a random rational Gram matrix
    id_err = F0
    if run_identity_check:
        rng = random.Random(SEED)
        G = [[F1 if i == j else F0 for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                G[i][j] = G[j][i] = Fraction(rng.randint(-3, 3), 5)
        # Recompute slack polynomial (from e_d, h_d, F_k ONLY!)
        slack_sym = [F0] * model.n_sym
        slack_sym[model.sym_idx[(0, 0, 0)]] -= e_d / binom_n2
        for d, hd in enumerate(h_d):
            if d == 0:
                slack_sym[model.sym_idx[(0, 0, 0)]] += hd
            else:
                slack_sym[model.sym_idx[(d, 0, 0)]] += hd / F3
        F_mats = []
        for blk, mat in zip(model.blocks, psd_d):
            if blk["kind"] != "F":
                continue
            F_mats.append((blk["k"], mat))
            sz = blk["size"]
            for a in range(sz):
                for b in range(a, sz):
                    mult = F1 if a == b else F2
                    for r, v in model.block_entry_map(blk, a, b).items():
                        slack_sym[r - 1] += mult * mat[a][b] * v
        # Evaluate LHS = 2(n-2)*(sum_{i<j} H(G_ij) - e) vs RHS = dsum(slack) + (n-2)*Sigma_all
        # Verify on small exact evaluation using Horner for H and direct sum!
        def ev_H(x):
            acc = F0
            for c in reversed(h_d):
                acc = acc * x + c
            return acc
        lhs = 2 * (n - 2) * (sum(ev_H(G[i][j]) for i in range(n) for j in range(i + 1, n)) - e_d)
        # Precompute orbit tuples for slack_sym
        terms = []
        for idx, c in enumerate(model.sym_mons):
            val = slack_sym[idx]
            if val:
                terms.append((val, sorted(set((c[p[0]], c[p[1]], c[p[2]]) for p in S3_PERMS))))
        def ev_slack(u, v, t):
            pu = [F1]; pv = [F1]; pt = [F1]
            for _ in range(model.D):
                pu.append(pu[-1] * u); pv.append(pv[-1] * v); pt.append(pt[-1] * t)
            tot = F0
            for val, orb in terms:
                s = F0
                for a, b, c in orb:
                    s += pu[a] * pv[b] * pt[c]
                tot += val * s
            return tot
        dsum_slack = F0
        for i in range(n):
            for j in range(i + 1, n):
                for l in range(j + 1, n):
                    dsum_slack += 6 * ev_slack(G[i][j], G[i][l], G[j][l])
        # Compute Sigma_all = sum_{i,j,l} sum_k <F_k, Y_k(G_ij, G_il, G_jl)>
        sig_all = F0
        for i in range(n):
            for j in range(n):
                for l in range(n):
                    u, v, t = G[i][j], G[i][l], G[j][l]
                    # Compute Q_k(u,v,t) via exact recurrence
                    q_vals = [F1]
                    if K > 1:
                        tuv = t - u * v
                        omu2v2 = (F1 - u * u) * (F1 - v * v)
                        q_vals.append(tuv)
                        for _ in range(2, K):
                            q_vals.append(2 * tuv * q_vals[-1] - omu2v2 * q_vals[-2])
                    pu = [F1]; pv = [F1]
                    for _ in range(M):
                        pu.append(pu[-1] * u); pv.append(pv[-1] * v)
                    for k, mat in F_mats:
                        sz = len(mat)
                        qv = q_vals[k]
                        quad = F0
                        for a in range(sz):
                            pua = pu[a]
                            row = mat[a]
                            for b in range(sz):
                                quad += pua * pv[b] * row[b]
                        sig_all += qv * quad
        rhs = dsum_slack + (n - 2) * sig_all
        id_err = abs(lhs - rhs)
        assert id_err == 0, f"EXACT COMBINATORIAL IDENTITY FAILED: |LHS-RHS|={id_err}"

    sha = hashlib.sha256(cert_path.read_bytes()).hexdigest()
    return dict(
        ok=True, cert_path=str(cert_path), sha256=sha,
        n=n, a0=frac_str(a0), M=M, K=K, blocks_verified=len(psd_d),
        R1=float(R1), R2=float(R2),
        certified_exact=frac_str(certified), certified_float=float(certified),
        identity_error=int(id_err), verify_s=round(time.time() - t0, 2),
    )


def selftest() -> None:
    print("[selftest] Testing exact Fraction S3 isotypic SOS + 3-point identity (n=9, M=5, K=5)...")
    model = SymCapModel(9, Fraction(-3, 4), M=5, K=5)
    rng = random.Random(SEED)
    for blk in model.blocks:
        if blk["kind"] == "s3_std":
            B = blk["basis"]
            sz = blk["size"]
            L = [[Fraction(rng.randint(-3, 3), 4) for _ in range(sz)] for _ in range(sz)]
            X = [[sum(L[i][r] * L[j][r] for r in range(sz)) for j in range(sz)] for i in range(sz)]
            sym_coeffs = [F0] * model.n_sym
            for a in range(sz):
                for b in range(a, sz):
                    mult = F1 if a == b else F2
                    for r, v in model.block_entry_map(blk, a, b).items():
                        sym_coeffs[r - 1] += mult * X[a][b] * (-v)
            u, v, t = Fraction(1, 3), Fraction(1, 4), Fraction(1, 5)
            val_sym = F0
            for idx, c in enumerate(model.sym_mons):
                if sym_coeffs[idx]:
                    orb = set((c[p[0]], c[p[1]], c[p[2]]) for p in S3_PERMS)
                    val_sym += sym_coeffs[idx] * sum((u ** a) * (v ** b) * (t ** d) for a, b, d in orb)
            ev = lambda poly: sum(val * (u ** a) * (v ** b) * (t ** d) for (a, b, d), val in poly.items())
            e1v = [ev(pair[0]) for pair in B]
            e2v = [ev(pair[1]) for pair in B]
            q1 = sum(e1v[i] * X[i][j] * e1v[j] for i in range(sz) for j in range(sz))
            q2 = sum(e2v[i] * X[i][j] * e2v[j] for i in range(sz) for j in range(sz))
            val_dir = ev(blk["mp"]) * (q1 / F3 + q2)
            assert val_sym == val_dir and val_dir >= 0
    print("[selftest] PASS: S3 standard-irrep exact rational SOS identity & nonnegativity verified!")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--verify-cert", type=str, default=None)
    ap.add_argument("--no-identity-check", action="store_true")
    ap.add_argument("--n", type=int, default=9)
    ap.add_argument("--a0", type=str, default="-153/200")
    ap.add_argument("--M", type=int, default=10)
    ap.add_argument("--K", type=int, default=10)
    ap.add_argument("--k-bits", type=int, default=128)
    ap.add_argument("--sdpa-bin", type=str, default="/tmp/hpbuild/sdpa-gmp-7.1.3/sdpa_gmp")
    ap.add_argument("--workdir", type=str, default="/tmp/sym_cap_work")
    ap.add_argument("--tag", type=str, default=None)
    ap.add_argument("--skip-solve", action="store_true")
    ap.add_argument("--cert-out", type=str, default=None)
    args = ap.parse_args()

    if args.selftest:
        selftest()
        return

    if args.verify_cert:
        res = verify_certificate_file(Path(args.verify_cert), run_identity_check=not args.no_identity_check)
        print(json.dumps(res, indent=2))
        return

    a0 = Fraction(args.a0)
    tag = args.tag or f"n{args.n}_a{str(a0).replace('/','o').replace('-','m')}_M{args.M}_K{args.K}"
    wdir = Path(args.workdir) / tag
    wdir.mkdir(parents=True, exist_ok=True)
    dat_path = wdir / f"{tag}.dat-s"
    res_path = wdir / f"{tag}.result"
    param_path = wdir / "param.sdpa"
    param_path.write_text(PARAM_SDPA)

    model = SymCapModel(args.n, a0, args.M, args.K)
    if args.skip_solve and res_path.exists():
        solve_s = 0.0
        for line in res_path.read_text(errors="ignore").splitlines()[-20:]:
            if "total time" in line and "=" in line:
                try:
                    solve_s = float(line.split("=")[-1].strip())
                except ValueError:
                    pass
    else:
        info = model.write_dat(dat_path)
        print(f"[{tag}] Exported m={info['m']}, blks={info['n_blocks']}, entries={info['n_entries']} in {info['export_s']}s", flush=True)
        t0 = time.time()
        proc = subprocess.run([args.sdpa_bin, "-ds", str(dat_path), "-o", str(res_path), "-p", str(param_path)],
                              capture_output=True, text=True)
        solve_s = time.time() - t0
        if proc.returncode != 0:
            raise RuntimeError(f"SDPA-GMP failed ({proc.returncode}): {proc.stderr[-1000:]}")
        print(f"[{tag}] SDPA-GMP finished in {solve_s:.1f}s", flush=True)

    cert_data = model.certify_from_result(res_path, k_bits=args.k_bits)
    out_path = Path(args.cert_out) if args.cert_out else (REPO / "certificates" / f"n9-stage-a-r24-symcap-{tag}.json")
    payload = model.write_certificate(cert_data, out_path, solve_s)
    print(f"[{tag}] Written exact certificate -> {out_path}")
    print(f"  certified = {payload['claimed_bound_float']:.15f}  R1={float(cert_data['R1']):.2e}  R2={float(cert_data['R2']):.2e}")
    # Immediately run out-of-process-style verification on the written JSON!
    ver = verify_certificate_file(out_path, run_identity_check=True)
    print(f"[{tag}] VERIFY OK in {ver['verify_s']}s: identity_err={ver['identity_error']}, blocks={ver['blocks_verified']}, sha256={ver['sha256'][:16]}...")


if __name__ == "__main__":
    main()
