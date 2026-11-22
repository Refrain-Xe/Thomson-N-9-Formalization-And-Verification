#!/usr/bin/env python3
"""export_lean_stage_b.py — Self-verifying Lean 4 certificate exporter for Thomson N=9 Stage B.

Reads the two exact rational SDP certificates inside thomson-n9/certificates/:
  1. n9-stage-b-symslab-m1_m090_M6K6.json      (covers [-1, -9/10])
  2. n9-stage-a-r24-symcap-m090_M10K10.json   (covers [-9/10, 1])

Converts every PSD block via high-precision Cholesky rounding into exact zero-Delta integer
Cholesky factors, pre-verifies EVERY Kronecker identity, degree bound, L1 bound, 1D minorant
identity, and 7-piece Bernstein L3 tube-forcing certificate in exact Python integer arithmetic,
and emits Lean 4 modules under thomson-n9/formal/lean/ThomsonN9/StageB/:
  - SlabCertData.lean
  - CapCertHarmData.lean
  - CapCertSosData.lean
  - CapCertBernData.lean
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

import mpmath as mp

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
LEAN_STAGEB = REPO / "formal" / "lean" / "ThomsonN9" / "StageB"
sys.path.insert(0, str(HERE))

from sym_cap_sdpa import (  # noqa: E402
    F0, F1, F2, F3, S3_PERMS,
    SymCapModel, build_s3_isotypic_bases_exact, build_s2_vt_bases_exact,
    poly_mul, poly_add,
)
from sym_strip_sdpa import (  # noqa: E402
    SymStripModel, build_s2_uv_bases_exact, monoms_3d_full,
)

# Canonical shared rational upper bound on E(triCapPrism z*):
# E(z*) = 25.75998653126983156407570227...
# E_ttp_hi = 25.7599865312698317 = E(z*) + 1.359e-16
E_TTP_HI_NUM = 257599865312698317
E_TTP_HI_DEN = 10000000000000000
E_TTP_HI = Fraction(E_TTP_HI_NUM, E_TTP_HI_DEN)

# Exact rational nu containers from TableB1Data.lean (verified verbatim against TableB1Data.lean)
NU_CONTAINERS = [
    (Fraction(-373780527846101896475859545040422561326456898875252340943916452473648470711253821718855761,
              500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
     Fraction(-93445064856350658642194375951527242099350870124512289674385202473648470711253821718855761,
              125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)),
    (Fraction(-1141807181114071074791597250713687405185622558906879142679459,
              1606938044258990275541962092341162602522202993782792835301376),
     Fraction(-1141805967021713074672581461757591416599246201137984251436193,
              1606938044258990275541962092341162602522202993782792835301376)),
    (Fraction(-1, 2), Fraction(-1, 2)),
    (Fraction(1219472153898103524140454959577438673543101124747659056083547526351529288746178281144239,
              125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
     Fraction(304935143649341357805624048472757900649129875487710325614797526351529288746178281144239,
              31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)),
    (Fraction(30335194569051975926583127854581726298052610373536869023155607420945412133761465156567283,
              125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
     Fraction(121341583538305689427578635121267683979370696625757022831749357420945412133761465156567283,
              500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)),
    (Fraction(1141805967021713074672581461757591416599246201137984251436193,
              3213876088517980551083924184682325205044405987565585670602752),
     Fraction(1141807181114071074791597250713687405185622558906879142679459,
              3213876088517980551083924184682325205044405987565585670602752)),
]


# ---------------------------------------------------------------------------
# Exact Integer / Polynomial Helpers matching PolyKron.lean 1-to-1
# ---------------------------------------------------------------------------

def load_utri_matrix(bj: dict) -> list[list[Fraction]]:
    sz = bj["size"]
    mat = [[F0] * sz for _ in range(sz)]
    for i in range(sz):
        for off, s in enumerate(bj["utri"][i]):
            v = Fraction(s)
            mat[i][i + off] = v
            mat[i + off][i] = v
    return mat


def cholesky_cols_int(mat_frac: list[list[Fraction]], B: int):
    """Compute lower-triangular Cholesky L with L L^T = mat_frac, round L_int = round(2^B * L),
    and return (cols_sparse, cols_dense, M_rec_frac) where cols are columns of L_int."""
    mp.mp.dps = 100
    n = len(mat_frac)
    A = mp.matrix([[mp.mpf(x.numerator) / x.denominator for x in row] for row in mat_frac])
    L = mp.cholesky(A)
    S = 1 << B
    # Columns k = 0..n-1: col k has entries (i, L_int[i, k]) for i = k..n-1
    cols_sparse: list[list[tuple[int, int]]] = []
    cols_dense: list[list[int]] = []
    L_int = [[0] * n for _ in range(n)]
    for k in range(n):
        col_sp = []
        col_dn = [0] * n
        for i in range(k, n):
            v = int(mp.nint(L[i, k] * S))
            L_int[i][k] = v
            col_dn[i] = v
            if v != 0:
                col_sp.append((i, v))
        if col_sp:
            cols_sparse.append(col_sp)
            # trim trailing zeros for 1D polynomial cols
            while col_dn and col_dn[-1] == 0:
                col_dn.pop()
            cols_dense.append(col_dn)
    S2 = Fraction(1, 1 << (2 * B))
    M_rec = [[F0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            s = 0
            for k in range(min(i, j) + 1):
                s += L_int[i][k] * L_int[j][k]
            M_rec[i][j] = Fraction(s) * S2
    return cols_sparse, cols_dense, M_rec


def scale_poly_to_int(p: dict[tuple[int, int, int], Fraction], scale: int) -> list[tuple[int, int, int, int]]:
    out = []
    for (a, b, c), v in sorted(p.items()):
        sv = v * scale
        assert sv.denominator == 1, f"Non-integer scaled coeff {sv} at {(a,b,c)}"
        if sv.numerator != 0:
            out.append((sv.numerator, a, b, c))
    return out


def poly3_to_dict(p: list[tuple[int, int, int, int]]) -> dict[tuple[int, int, int], int]:
    d: dict[tuple[int, int, int], int] = {}
    for c, a, b, e in p:
        if c:
            d[(a, b, e)] = d.get((a, b, e), 0) + c
    return {k: v for k, v in d.items() if v}


def dict_to_poly3(d: dict[tuple[int, int, int], int]) -> list[tuple[int, int, int, int]]:
    return [(v, a, b, c) for (a, b, c), v in sorted(d.items()) if v != 0]


def dict_add(d1: dict, d2: dict, mult: int = 1) -> dict:
    out = dict(d1)
    for k, v in d2.items():
        nv = out.get(k, 0) + mult * v
        if nv:
            out[k] = nv
        else:
            out.pop(k, None)
    return out


def dict_mul(d1: dict, d2: dict) -> dict:
    out: dict = {}
    for (a1, b1, c1), v1 in d1.items():
        for (a2, b2, c2), v2 in d2.items():
            key = (a1 + a2, b1 + b2, c1 + c2)
            nv = out.get(key, 0) + v1 * v2
            if nv:
                out[key] = nv
            else:
                out.pop(key, None)
    return out


def dict_perm(d: dict, perm: tuple[int, int, int]) -> dict:
    """Substitute (u, v, t) -> (vars[perm[0]], vars[perm[1]], vars[perm[2]]).
    For monomial u^e0 v^e1 t^e2:
      u -> var[perm[0]], v -> var[perm[1]], t -> var[perm[2]].
    Wait: check carefully!
      If f(u,v,t) = u^a v^b t^c, then f(v,t,u) = v^a t^b u^c = u^c v^a t^b!
      Here perm = (1, 2, 0) means old_slot 0 -> new_slot 1, old_slot 1 -> new_slot 2, old_slot 2 -> new_slot 0!
    """
    out: dict = {}
    for e, v in d.items():
        ne = [0, 0, 0]
        ne[perm[0]] += e[0]
        ne[perm[1]] += e[1]
        ne[perm[2]] += e[2]
        key = (ne[0], ne[1], ne[2])
        nv = out.get(key, 0) + v
        if nv:
            out[key] = nv
        else:
            out.pop(key, None)
    return out


def kev3_shift(eu: int, ev: int, et: int, p: list[tuple[int, int, int, int]]) -> int:
    acc = 0
    for c, a, b, d in p:
        acc += c << (eu * a + ev * b + et * d)
    return acc


def pevalZ(p: list[int], y: int) -> int:
    acc = 0
    for c in reversed(p):
        acc = c + y * acc
    return acc


def q3Z(k: int, U: int, V: int, T: int) -> int:
    if k == 0:
        return 1
    if k == 1:
        return T - U * V
    q0 = 1
    q1 = T - U * V
    a = 2 * (T - U * V)
    b = (1 - U * U) * (1 - V * V)
    for _ in range(2, k + 1):
        q0, q1 = q1, a * q1 - b * q0
    return q1


def q3L1(k: int) -> int:
    if k == 0:
        return 1
    if k == 1:
        return 2
    a, b = 1, 2
    for _ in range(2, k + 1):
        a, b = b, 4 * b + 4 * a
    return b


def harm_blk_kev_shift(eu: int, ev: int, et: int, k: int, cols: list[list[tuple[int, int]]]) -> int:
    U, V, T = 1 << eu, 1 << ev, 1 << et
    qk = q3Z(k, U, V, T)
    sp = 0
    for col in cols:
        su = sum(c << (eu * a) for a, c in col)
        sv = sum(c << (ev * a) for a, c in col)
        sp += su * sv
    return qk * sp


def harm_list_kev_shift(eu: int, ev: int, et: int, blks: list[tuple[int, int, list[list[tuple[int, int]]]]]) -> int:
    return sum(harm_blk_kev_shift(eu, ev, et, k, cols) for k, _, cols in blks)


def harm_list_l1(blks: list[tuple[int, int, list[list[tuple[int, int]]]]]) -> int:
    tot = 0
    for k, _, cols in blks:
        ss = 0
        for col in cols:
            s = sum(abs(c) for _, c in col)
            ss += s * s
        tot += q3L1(k) * ss
    return tot


def chol_plain_kev_shift(eu: int, ev: int, et: int, mult: int, mp_p: list, basis: list, cols: list) -> int:
    bvals = [kev3_shift(eu, ev, et, b) for b in basis]
    ss = 0
    for col in cols:
        s = sum(c * bvals[idx] for idx, c in col)
        ss += s * s
    return mult * kev3_shift(eu, ev, et, mp_p) * ss


def chol_plain_l1(mult: int, mp_p: list, basis: list, cols: list) -> int:
    bl1 = [sum(abs(c) for c, _, _, _ in b) for b in basis]
    ss = 0
    for col in cols:
        s = sum(abs(c) * bl1[idx] for idx, c in col)
        ss += s * s
    return mult * sum(abs(c) for c, _, _, _ in mp_p) * ss


def chol_std_kev(w: int, D: int, mp_p: list, e1: list, e2: list, cols: list) -> int:
    eu, ev, et = w, w * D, w * D * D
    v1 = [kev3_shift(eu, ev, et, b) for b in e1]
    v2 = [kev3_shift(eu, ev, et, b) for b in e2]
    ss = 0
    for col in cols:
        s1 = sum(c * v1[idx] for idx, c in col)
        s2 = sum(c * v2[idx] for idx, c in col)
        ss += s1 * s1 + 3 * s2 * s2
    return kev3_shift(eu, ev, et, mp_p) * ss


def chol_std_l1(mp_p: list, e1: list, e2: list, cols: list) -> int:
    l1_1 = [sum(abs(c) for c, _, _, _ in b) for b in e1]
    l1_2 = [sum(abs(c) for c, _, _, _ in b) for b in e2]
    ss = 0
    for col in cols:
        s1 = sum(abs(c) * l1_1[idx] for idx, c in col)
        s2 = sum(abs(c) * l1_2[idx] for idx, c in col)
        ss += s1 * s1 + 3 * s2 * s2
    return sum(abs(c) for c, _, _, _ in mp_p) * ss


def padd_1d(p: list[int], q: list[int]) -> list[int]:
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def pscale_1d(c: int, p: list[int]) -> list[int]:
    return [c * x for x in p]


def pmul_1d(p: list[int], q: list[int]) -> list[int]:
    if not p or not q:
        return []
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                if b:
                    out[i + j] += a * b
    return out


def chol1d_poly(cols: list[list[int]]) -> list[int]:
    acc: list[int] = []
    for col in cols:
        acc = padd_1d(acc, pmul_1d(col, col))
    return acc


def two_y_H_1m2y2(h_int: list[int]) -> list[int]:
    """Compute exact 1D polynomial 2y * H_int(1 - 2y^2) as list of integer coeffs."""
    out = [0] * (2 * len(h_int))
    for d, hd in enumerate(h_int):
        if not hd:
            continue
        for j in range(d + 1):
            c = 2 * math.comb(d, j) * ((-2) ** j) * hd
            out[2 * j + 1] += c
    while out and out[-1] == 0:
        out.pop()
    return out


# ---------------------------------------------------------------------------
# Lean Formatting Helpers
# ---------------------------------------------------------------------------

def fmt_list_int(xs: list[int]) -> str:
    return "[" + ", ".join(str(x) for x in xs) + "]"


def fmt_poly3(p: list[tuple[int, int, int, int]]) -> str:
    return "[" + ", ".join(f"({c}, {a}, {b}, {d})" for c, a, b, d in p) + "]"


def fmt_basis_arr(basis: list[list[tuple[int, int, int, int]]]) -> str:
    items = [fmt_poly3(b) for b in basis]
    return "#[\n    " + ",\n    ".join(items) + "\n  ]"


def fmt_cols_arr(cols: list[list[tuple[int, int]]]) -> str:
    items = ["[" + ", ".join(f"({i}, {c})" for i, c in col) + "]" for col in cols]
    return "#[\n    " + ",\n    ".join(items) + "\n  ]"


def fmt_cols_1d(cols: list[list[int]]) -> str:
    items = [fmt_list_int(c) for c in cols]
    return "[\n  " + ",\n  ".join(items) + "\n]"


def fmt_harm_blk(k: int, m: int, cols: list[list[tuple[int, int]]]) -> str:
    return f"{{ k := {k}, m := {m}, cols := {fmt_cols_arr(cols)} }}"


def fmt_plain_blk(mult: int, mp_p: list, basis: list, cols: list) -> str:
    return (
        "{\n"
        f"  mult := {mult},\n"
        f"  mp := {fmt_poly3(mp_p)},\n"
        f"  basis := {fmt_basis_arr(basis)},\n"
        f"  cols := {fmt_cols_arr(cols)}\n"
        "}"
    )


def fmt_std_blk(mp_p: list, e1: list, e2: list, cols: list) -> str:
    return (
        "{\n"
        f"  mp := {fmt_poly3(mp_p)},\n"
        f"  e1 := {fmt_basis_arr(e1)},\n"
        f"  e2 := {fmt_basis_arr(e2)},\n"
        f"  cols := {fmt_cols_arr(cols)}\n"
        "}"
    )


# ---------------------------------------------------------------------------
# Build exact 3D polynomial dict from Cholesky blocks (for exact residual extraction)
# ---------------------------------------------------------------------------

def harm_list_to_dict(Q_polys: list[dict], blks: list[tuple[int, int, list[list[tuple[int, int]]]]]) -> dict:
    """Exact integer 3D dict for harmListEv blks (u, v, t)."""
    tot: dict = {}
    for k, _, cols in blks:
        qk = {e: int(v) for e, v in Q_polys[k].items()}
        # sum_col (col(u) * col(v))
        uv_dict: dict = {}
        for col in cols:
            for a, ca in col:
                for b, cb in col:
                    key = (a, b, 0)
                    uv_dict[key] = uv_dict.get(key, 0) + ca * cb
        uv_dict = {e: v for e, v in uv_dict.items() if v}
        tot = dict_add(tot, dict_mul(qk, uv_dict))
    return tot


def eval_g_int_dict(s_dict: dict) -> list[int]:
    """g(x) = s(1,x,x) + s(x,1,x) + s(x,x,1) as 1D integer coeff list."""
    out: dict[int, int] = {}
    for (a, b, c), v in s_dict.items():
        for d in (b + c, a + c, a + b):
            out[d] = out.get(d, 0) + v
    if not out:
        return []
    md = max(out)
    res = [out.get(i, 0) for i in range(md + 1)]
    while res and res[-1] == 0:
        res.pop()
    return res


def plain_blk_to_dict(mult: int, mp_p: list, basis: list, cols: list) -> dict:
    b_dicts = [poly3_to_dict(b) for b in basis]
    ss: dict = {}
    for col in cols:
        lin: dict = {}
        for idx, c in col:
            lin = dict_add(lin, b_dicts[idx], c)
        ss = dict_add(ss, dict_mul(lin, lin))
    return dict_mul(poly3_to_dict([(mult * c, a, b, d) for c, a, b, d in mp_p]), ss)


def std_blk_to_dict(mp_p: list, e1: list, e2: list, cols: list) -> dict:
    d1 = [poly3_to_dict(b) for b in e1]
    d2 = [poly3_to_dict(b) for b in e2]
    ss: dict = {}
    for col in cols:
        l1: dict = {}
        l2: dict = {}
        for idx, c in col:
            l1 = dict_add(l1, d1[idx], c)
            l2 = dict_add(l2, d2[idx], c)
        ss = dict_add(ss, dict_mul(l1, l1), 1)
        ss = dict_add(ss, dict_mul(l2, l2), 3)
    return dict_mul(poly3_to_dict(mp_p), ss)


def list_1d_to_dict(p: list[int], var: int) -> dict:
    out = {}
    for d, c in enumerate(p):
        if c:
            e = [0, 0, 0]
            e[var] = d
            out[tuple(e)] = c
    return out


# ---------------------------------------------------------------------------
# PART 1: Export SlabCertData.lean
# ---------------------------------------------------------------------------

def export_slab(B: int = 36, D_kron: int = 12):
    t0 = time.time()
    print(f"\n=== Exporting SlabCertData.lean (B={B}, D={D_kron}) ===")
    slab_path = REPO / "certificates" / "n9-stage-b-symslab-m1_m090_M6K6.json"
    raw = json.loads(slab_path.read_text())
    lo, hi = Fraction(raw["lo"]), Fraction(raw["hi"])
    M, K = int(raw["M"]), int(raw["K"])
    assert lo == Fraction(-1) and hi == Fraction(-9, 10) and M == 6 and K == 6
    model = SymStripModel(lo, hi, M, K)

    S = 1 << B
    S2 = 1 << (2 * B)
    rS2 = lambda q: int(round(q * S2))
    e_int = math.floor(Fraction(raw["e"]) * S2)
    hA_int = [rS2(Fraction(x)) for x in raw["h_A"]]
    hB_int = [rS2(Fraction(x)) for x in raw["h_B"]]
    hC_int = [rS2(Fraction(x)) for x in raw["h_C"]]
    psiBa_int = [rS2(Fraction(x)) for x in raw["psi_Ba"]]
    psiCb_int = [rS2(Fraction(x)) for x in raw["psi_Cb"]]
    ca_int = rS2(Fraction(raw["c_a"]))
    cb_int = rS2(Fraction(raw["c_b"]))

    # Map blocks by name
    bj_map = {b["name"]: b for b in raw["blocks"]}
    spec_map = {b["name"]: b for b in model.blocks}

    harmP = []
    harmR = []
    for k in range(K):
        for typ, dst in (("P", harmP), ("R", harmR)):
            name = f"F_{typ}_{k}"
            mat = load_utri_matrix(bj_map[name])
            cols_sp, _, _ = cholesky_cols_int(mat, B)
            dst.append((k, M - k, cols_sp))

    sP_dict = harm_list_to_dict(model.Q, harmP)
    sR_dict = harm_list_to_dict(model.Q, harmR)
    sP111_int = sum(sP_dict.values())
    sR111_int = sum(sR_dict.values())
    assert sP111_int == harm_list_kev_shift(0, 0, 0, harmP)
    assert sR111_int == harm_list_kev_shift(0, 0, 0, harmR)
    gP_int = eval_g_int_dict(sP_dict)
    gR_int = eval_g_int_dict(sR_dict)

    # Exact normalization: c_g = cg_int / (35 * S^2)
    cg_int = e_int + 2 * sP111_int + 7 * sR111_int - 7 * ca_int - 42 * cb_int

    # Helper to build SOS blocks
    def mk_plain(name: str, mult: int, mp_scale: int, basis_scale: int):
        spec = spec_map[name]
        mat = load_utri_matrix(bj_map[name])
        cols_sp, _, _ = cholesky_cols_int(mat, B)
        mp_p = scale_poly_to_int(spec["mp"], mp_scale)
        basis_p = [scale_poly_to_int(b, basis_scale) for b in spec["basis"]]
        return (name, mult, mp_p, basis_p, cols_sp)

    def mk_std(name: str, mp_mult: int, basis_scale: int):
        spec = spec_map[name]
        mat = load_utri_matrix(bj_map[name])
        cols_sp, _, _ = cholesky_cols_int(mat, B)
        mp_p = scale_poly_to_int(spec["mp"], mp_mult)
        e1_p = [scale_poly_to_int(pair[0], basis_scale) for pair in spec["basis"]]
        e2_p = [scale_poly_to_int(pair[1], basis_scale) for pair in spec["basis"]]
        return (name, mp_p, e1_p, e2_p, cols_sp)

    # Orbit A (K_A = 280)
    sosA_sym = [
        mk_plain("SOS_A_1_even", 70, 1, 2),
        mk_plain("SOS_A_1_odd", 70, 1, 2),
        mk_plain("SOS_A_ulo_even", 70, 1, 2),
        mk_plain("SOS_A_ulo_odd", 70, 1, 2),
        mk_plain("SOS_A_hiu_even", 7, 10, 2),
        mk_plain("SOS_A_hiu_odd", 7, 10, 2),
        mk_plain("SOS_A_detG_even", 70, 1, 2),
        mk_plain("SOS_A_detG_odd", 70, 1, 2),
    ]
    sosA_asym = [
        mk_plain("SOS_A_vlo", 140, 1, 1),
        mk_plain("SOS_A_vhi", 140, 1, 1),
    ]

    # Orbit B (K_B = 12)
    sosB_sym = [
        mk_plain("SOS_B_1_even", 3, 1, 2),
        mk_plain("SOS_B_1_odd", 3, 1, 2),
        mk_plain("SOS_B_tlo_even", 3, 1, 2),
        mk_plain("SOS_B_tlo_odd", 3, 1, 2),
        mk_plain("SOS_B_thi_even", 3, 1, 2),
        mk_plain("SOS_B_thi_odd", 3, 1, 2),
        mk_plain("SOS_B_detG_even", 3, 1, 2),
        mk_plain("SOS_B_detG_odd", 3, 1, 2),
    ]
    sosB_asym = [
        mk_plain("SOS_B_ulo", 6, 1, 1),
        mk_plain("SOS_B_uhi", 6, 1, 1),
    ]

    # Orbit G (K_G = 1260)
    sosG_s3_plain = [
        mk_plain("SOS_G_1_triv", 35, 1, 6),
        mk_plain("SOS_G_1_sign", 35, 1, 6),
        mk_plain("SOS_G_detG_triv", 35, 1, 6),
        mk_plain("SOS_G_detG_sign", 35, 1, 6),
    ]
    sosG_s3_std = [
        mk_std("SOS_G_1_std", 105, 2),
        mk_std("SOS_G_detG_std", 105, 2),
    ]
    sosG_s2 = [
        mk_plain("SOS_G_ulo_even", 105, 1, 2),
        mk_plain("SOS_G_ulo_odd", 105, 1, 2),
        mk_plain("SOS_G_uhi_even", 105, 1, 2),
        mk_plain("SOS_G_uhi_odd", 105, 1, 2),
    ]

    # Compute exact integer residuals resA, resB, resG!
    # 280 * S^2 * lam_A(u,v,t):
    lamA_d: dict = {}
    lamA_d = dict_add(lamA_d, list_1d_to_dict(hA_int, 0), 40)
    lamA_d = dict_add(lamA_d, list_1d_to_dict(psiBa_int, 1), 280)
    lamA_d = dict_add(lamA_d, list_1d_to_dict(psiBa_int, 2), 280)
    lamA_d = dict_add(lamA_d, {(0, 0, 0): -280 * ca_int}, 1)
    lamA_d = dict_add(lamA_d, list_1d_to_dict(gP_int, 0), -80)
    lamA_d = dict_add(lamA_d, sP_dict, -560)
    lamA_d = dict_add(lamA_d, dict_perm(sP_dict, (0, 2, 1)), -560)  # sP(u, t, v)
    # sR(v, t, u): old u->v(1), old v->t(2), old t->u(0) => perm=(1, 2, 0)
    lamA_d = dict_add(lamA_d, dict_perm(sR_dict, (1, 2, 0)), -560)

    sosA_d: dict = {}
    for _, mult, mp_p, bas, cols in sosA_sym:
        sosA_d = dict_add(sosA_d, plain_blk_to_dict(mult, mp_p, bas, cols))
    for _, mult, mp_p, bas, cols in sosA_asym:
        bd = plain_blk_to_dict(mult, mp_p, bas, cols)
        sosA_d = dict_add(sosA_d, bd)
        sosA_d = dict_add(sosA_d, dict_perm(bd, (0, 2, 1)))  # (u, t, v)
    resA_p = dict_to_poly3(dict_add(lamA_d, sosA_d, -1))

    # 12 * S^2 * lam_B(u,v,t):
    hB_m_psi = padd_1d(hB_int, pscale_1d(-1, psiBa_int))
    lamB_d: dict = {}
    lamB_d = dict_add(lamB_d, list_1d_to_dict(hB_m_psi, 0), 2)
    lamB_d = dict_add(lamB_d, list_1d_to_dict(hB_m_psi, 1), 2)
    lamB_d = dict_add(lamB_d, list_1d_to_dict(psiCb_int, 2), 12)
    lamB_d = dict_add(lamB_d, {(0, 0, 0): -12 * cb_int}, 1)
    lamB_d = dict_add(lamB_d, list_1d_to_dict(gP_int, 0), -2)
    lamB_d = dict_add(lamB_d, list_1d_to_dict(gP_int, 1), -2)
    lamB_d = dict_add(lamB_d, list_1d_to_dict(gR_int, 0), -2)
    lamB_d = dict_add(lamB_d, list_1d_to_dict(gR_int, 1), -2)
    lamB_d = dict_add(lamB_d, sP_dict, -24)
    # sR(u, t, v): perm=(0, 2, 1); sR(v, t, u): perm=(1, 2, 0)
    lamB_d = dict_add(lamB_d, dict_perm(sR_dict, (0, 2, 1)), -24)
    lamB_d = dict_add(lamB_d, dict_perm(sR_dict, (1, 2, 0)), -24)

    sosB_d: dict = {}
    for _, mult, mp_p, bas, cols in sosB_sym:
        sosB_d = dict_add(sosB_d, plain_blk_to_dict(mult, mp_p, bas, cols))
    for _, mult, mp_p, bas, cols in sosB_asym:
        bd = plain_blk_to_dict(mult, mp_p, bas, cols)
        sosB_d = dict_add(sosB_d, bd)
        sosB_d = dict_add(sosB_d, dict_perm(bd, (1, 0, 2)))  # (v, u, t)
    resB_p = dict_to_poly3(dict_add(lamB_d, sosB_d, -1))

    # 1260 * S^2 * lam_G(u,v,t):
    hC_m_2psi = padd_1d(hC_int, pscale_1d(-2, psiCb_int))
    lamG_d: dict = {}
    for var in (0, 1, 2):
        lamG_d = dict_add(lamG_d, list_1d_to_dict(hC_m_2psi, var), 252)
        lamG_d = dict_add(lamG_d, list_1d_to_dict(gR_int, var), -504)
    lamG_d = dict_add(lamG_d, {(0, 0, 0): -36 * cg_int}, 1)
    lamG_d = dict_add(lamG_d, sR_dict, -2520)
    lamG_d = dict_add(lamG_d, dict_perm(sR_dict, (0, 2, 1)), -2520)  # sR(u, t, v)
    lamG_d = dict_add(lamG_d, dict_perm(sR_dict, (1, 2, 0)), -2520)  # sR(v, t, u)

    sosG_d: dict = {}
    for _, mult, mp_p, bas, cols in sosG_s3_plain:
        sosG_d = dict_add(sosG_d, plain_blk_to_dict(mult, mp_p, bas, cols))
    for _, mp_p, e1, e2, cols in sosG_s3_std:
        sosG_d = dict_add(sosG_d, std_blk_to_dict(mp_p, e1, e2, cols))
    for _, mult, mp_p, bas, cols in sosG_s2:
        bd = plain_blk_to_dict(mult, mp_p, bas, cols)
        sosG_d = dict_add(sosG_d, bd)
        sosG_d = dict_add(sosG_d, dict_perm(bd, (1, 0, 2)))  # (v, u, t)
        # (t, u, v): old u->t(2), old v->u(0), old t->v(1) => perm=(2, 0, 1)
        sosG_d = dict_add(sosG_d, dict_perm(bd, (2, 0, 1)))  # (t, u, v)
    resG_p = dict_to_poly3(dict_add(lamG_d, sosG_d, -1))

    # 1D minorants
    def get_1d_cols(name: str) -> list[list[int]]:
        _, cols_dn, _ = cholesky_cols_int(load_utri_matrix(bj_map[name]), B)
        return cols_dn

    tauA = [get_1d_cols(f"tauA_{i}") for i in range(6)]
    sigB = [get_1d_cols(f"sigB_{i}") for i in range(4)]
    sigC = [get_1d_cols(f"sigC_{i}") for i in range(4)]

    # Check exact 1D residuals:
    # A (mult 20): 20*(2y*hA(1-2y^2) - S^2) + 20*tau0 + 20y*tau1 + (-19+20y^2)*tau2 + (20-20y^2)*tau3 + (-19y+20y^3)*tau4 + (20y-20y^3)*tau5
    mA_lhs = padd_1d(pscale_1d(20, padd_1d(two_y_H_1m2y2(hA_int), [-S2])),
             padd_1d(pscale_1d(20, chol1d_poly(tauA[0])),
             padd_1d(pmul_1d([0, 20], chol1d_poly(tauA[1])),
             padd_1d(pmul_1d([-19, 0, 20], chol1d_poly(tauA[2])),
             padd_1d(pmul_1d([20, 0, -20], chol1d_poly(tauA[3])),
             padd_1d(pmul_1d([0, -19, 0, 20], chol1d_poly(tauA[4])),
                     pmul_1d([0, 20, 0, -20], chol1d_poly(tauA[5]))))))))
    while mA_lhs and mA_lhs[-1] == 0:
        mA_lhs.pop()
    res_yA = mA_lhs

    def mk_minor_BC(h_int, sig):
        out = padd_1d(padd_1d(two_y_H_1m2y2(h_int), [-S2]),
              padd_1d(chol1d_poly(sig[0]),
              padd_1d(pmul_1d([0, 1], chol1d_poly(sig[1])),
              padd_1d(pmul_1d([1, 0, -1], chol1d_poly(sig[2])),
                      pmul_1d([0, 1, 0, -1], chol1d_poly(sig[3]))))))
        while out and out[-1] == 0:
            out.pop()
        return out

    res_yB = mk_minor_BC(hB_int, sigB)
    res_yC = mk_minor_BC(hC_int, sigC)

    # Compute exact L1 bounds for HasPolyRep3 (matching Lean formulas!)
    l1_l = lambda lst: sum(abs(x) for x in lst)
    l1_p3 = lambda p: sum(abs(c) for c, _, _, _ in p)
    l1_hP = harm_list_l1(harmP)
    l1_hR = harm_list_l1(harmR)

    L1_A = (40 * l1_l(hA_int) + 280 * l1_l(psiBa_int) + 280 * l1_l(psiBa_int) + 280 * abs(ca_int)
            + 80 * 3 * l1_hP + 560 * 2 * l1_hP + 560 * l1_hR
            + sum(chol_plain_l1(m, mp_p, b, c) for _, m, mp_p, b, c in sosA_sym)
            + 2 * sum(chol_plain_l1(m, mp_p, b, c) for _, m, mp_p, b, c in sosA_asym)
            + l1_p3(resA_p))
    L1_B = (2 * (l1_l(hB_int) + l1_l(psiBa_int)) + 2 * (l1_l(hB_int) + l1_l(psiBa_int))
            + 12 * l1_l(psiCb_int) + 12 * abs(cb_int)
            + 2 * 3 * l1_hP + 2 * 3 * l1_hP + 2 * 3 * l1_hR + 2 * 3 * l1_hR
            + 24 * l1_hP + 24 * 2 * l1_hR
            + sum(chol_plain_l1(m, mp_p, b, c) for _, m, mp_p, b, c in sosB_sym)
            + 2 * sum(chol_plain_l1(m, mp_p, b, c) for _, m, mp_p, b, c in sosB_asym)
            + l1_p3(resB_p))
    L1_G = (3 * 252 * (l1_l(hC_int) + 2 * l1_l(psiCb_int)) + 36 * abs(cg_int)
            + 3 * 504 * 3 * l1_hR + 2520 * 3 * l1_hR
            + sum(chol_plain_l1(m, mp_p, b, c) for _, m, mp_p, b, c in sosG_s3_plain)
            + sum(chol_std_l1(mp_p, e1, e2, c) for _, mp_p, e1, e2, c in sosG_s3_std)
            + 3 * sum(chol_plain_l1(m, mp_p, b, c) for _, m, mp_p, b, c in sosG_s2)
            + l1_p3(resG_p))
    w_slab = max(L1_A, L1_B, L1_G).bit_length() + 4

    # Pre-verify ALL 3 Kronecker evaluations == 0 in Python!
    eu, ev, et = w_slab, w_slab * D_kron, w_slab * D_kron * D_kron
    U, V, T = 1 << eu, 1 << ev, 1 << et
    gP_u = harm_list_kev_shift(0, eu, eu, harmP) + harm_list_kev_shift(eu, 0, eu, harmP) + harm_list_kev_shift(eu, eu, 0, harmP)
    gP_v = harm_list_kev_shift(0, ev, ev, harmP) + harm_list_kev_shift(ev, 0, ev, harmP) + harm_list_kev_shift(ev, ev, 0, harmP)
    gR_u = harm_list_kev_shift(0, eu, eu, harmR) + harm_list_kev_shift(eu, 0, eu, harmR) + harm_list_kev_shift(eu, eu, 0, harmR)
    gR_v = harm_list_kev_shift(0, ev, ev, harmR) + harm_list_kev_shift(ev, 0, ev, harmR) + harm_list_kev_shift(ev, ev, 0, harmR)
    gR_t = harm_list_kev_shift(0, et, et, harmR) + harm_list_kev_shift(et, 0, et, harmR) + harm_list_kev_shift(et, et, 0, harmR)

    lhsA = (40 * pevalZ(hA_int, U) + 280 * (pevalZ(psiBa_int, V) + pevalZ(psiBa_int, T)) - 280 * ca_int
            - 80 * gP_u
            - 560 * (harm_list_kev_shift(eu, ev, et, harmP) + harm_list_kev_shift(eu, et, ev, harmP))
            - 560 * harm_list_kev_shift(ev, et, eu, harmR))
    rhsA = (sum(chol_plain_kev_shift(eu, ev, et, m, mp_p, b, c) for _, m, mp_p, b, c in sosA_sym)
            + sum(chol_plain_kev_shift(eu, ev, et, m, mp_p, b, c) + chol_plain_kev_shift(eu, et, ev, m, mp_p, b, c)
                  for _, m, mp_p, b, c in sosA_asym)
            + kev3_shift(eu, ev, et, resA_p))
    assert lhsA == rhsA, f"SLAB KRON A FAILED!"

    lhsB = (2 * (pevalZ(hB_int, U) - pevalZ(psiBa_int, U) + pevalZ(hB_int, V) - pevalZ(psiBa_int, V))
            + 12 * pevalZ(psiCb_int, T) - 12 * cb_int
            - 2 * (gP_u + gP_v + gR_u + gR_v)
            - 24 * harm_list_kev_shift(eu, ev, et, harmP)
            - 24 * (harm_list_kev_shift(eu, et, ev, harmR) + harm_list_kev_shift(ev, et, eu, harmR)))
    rhsB = (sum(chol_plain_kev_shift(eu, ev, et, m, mp_p, b, c) for _, m, mp_p, b, c in sosB_sym)
            + sum(chol_plain_kev_shift(eu, ev, et, m, mp_p, b, c) + chol_plain_kev_shift(ev, eu, et, m, mp_p, b, c)
                  for _, m, mp_p, b, c in sosB_asym)
            + kev3_shift(eu, ev, et, resB_p))
    assert lhsB == rhsB, f"SLAB KRON B FAILED!"

    lhsG = (252 * (pevalZ(hC_int, U) - 2 * pevalZ(psiCb_int, U)
                   + pevalZ(hC_int, V) - 2 * pevalZ(psiCb_int, V)
                   + pevalZ(hC_int, T) - 2 * pevalZ(psiCb_int, T))
            - 36 * cg_int
            - 504 * (gR_u + gR_v + gR_t)
            - 2520 * (harm_list_kev_shift(eu, ev, et, harmR)
                      + harm_list_kev_shift(eu, et, ev, harmR)
                      + harm_list_kev_shift(ev, et, eu, harmR)))
    rhsG = (sum(chol_plain_kev_shift(eu, ev, et, m, mp_p, b, c) for _, m, mp_p, b, c in sosG_s3_plain)
            + sum(chol_std_kev(w_slab, D_kron, mp_p, e1, e2, c) for _, mp_p, e1, e2, c in sosG_s3_std)
            + sum(chol_plain_kev_shift(eu, ev, et, m, mp_p, b, c)
                  + chol_plain_kev_shift(ev, eu, et, m, mp_p, b, c)
                  + chol_plain_kev_shift(et, eu, ev, m, mp_p, b, c)
                  for _, m, mp_p, b, c in sosG_s2)
            + kev3_shift(eu, ev, et, resG_p))
    assert lhsG == rhsG, f"SLAB KRON G FAILED!"

    # Check exact final bound:
    # sumPairs9 >= (e - 7*R1A - 42*R1B - 35*R1G) / (1 + R2max) > E_TTP_HI
    R1A = Fraction(l1_p3(resA_p), 280 * S2)
    R1B = Fraction(l1_p3(resB_p), 12 * S2)
    R1G = Fraction(l1_p3(resG_p), 1260 * S2)
    R2A = Fraction(l1_l(res_yA), 20 * S2)
    R2B = Fraction(l1_l(res_yB), S2)
    R2C = Fraction(l1_l(res_yC), S2)
    R2max = max(R2A, R2B, R2C)
    e_frac = Fraction(e_int, S2)
    cert_slab = (e_frac - 7 * R1A - 42 * R1B - 35 * R1G) / (1 + R2max)
    assert cert_slab > E_TTP_HI, f"Slab bound {float(cert_slab)} <= E_TTP_HI!"
    # Exact integer inequality we'll check in Lean (clearing 1260 * 20 * S2 * E_TTP_HI_DEN):
    # Let R2_num = max(l1_l(res_yA), 20*l1_l(res_yB), 20*l1_l(res_yC)) so R2 <= R2_num / (20 * S2).
    # 7*R1A + 42*R1B + 35*R1G = (9*l1(resA) + 1260*l1(resB) + 10*l1(resG)) / (360 * S2)
    # Wait: 7/280 = 1/40 = 9/360; 42/12 = 7/2 = 1260/360; 35/1260 = 1/36 = 10/360!
    R1_num360 = 9 * l1_p3(resA_p) + 1260 * l1_p3(resB_p) + 10 * l1_p3(resG_p)
    R2_num20 = max(l1_l(res_yA), 20 * l1_l(res_yB), 20 * l1_l(res_yC))
    # E_TTP_HI * (1 + R2_num20/(20*S2)) < (360*e_int - R1_num360) / (360*S2)
    # <=> E_TTP_HI_NUM * 360 * (20*S2 + R2_num20) < E_TTP_HI_DEN * 20 * (360*e_int - R1_num360)
    # <=> E_TTP_HI_NUM * 18 * (20*S2 + R2_num20) < E_TTP_HI_DEN * (360*e_int - R1_num360)
    assert E_TTP_HI_NUM * 18 * (20 * S2 + R2_num20) < E_TTP_HI_DEN * (360 * e_int - R1_num360)

    print(f"  [OK] Pre-verified SLAB Kron A/B/G == 0 (w={w_slab}, D={D_kron})")
    print(f"       R1A={float(R1A):.2e}, R1B={float(R1B):.2e}, R1G={float(R1G):.2e}, R2max={float(R2max):.2e}")
    print(f"       cert={float(cert_slab):.12f} (margin={float(cert_slab - E_TTP_HI):+.6f})")

    # Write SlabCertData.lean
    lines = [
        "import ThomsonN9.StageB.PolyKron",
        "",
        "/-!",
        "# Thomson N = 9 Stage B — Slab Certificate Data (`[-1, -9/10]`, `M=6, K=6`)",
        "",
        "Auto-generated by `numerics/bounds/export_lean_stage_b.py` from",
        "`certificates/n9-stage-b-symslab-m1_m090_M6K6.json`. Zero-Δ integer Cholesky",
        "factors, exact Kronecker identities, and exact 1D Markov-Lukács minorants",
        "verified by Lean's kernel (`decide +kernel`).",
        "-/",
        "",
        "set_option maxHeartbeats 8000000",
        "set_option maxRecDepth 200000",
        "",
        "namespace ThomsonN9.StageB.SlabCertData",
        "",
        "open ThomsonN9.StageB.PolyKron",
        "",
        f"def B_bits : ℕ := {B}",
        f"def S2 : ℤ := {S2}",
        f"def D_kron : ℕ := {D_kron}",
        f"def w_kron : ℕ := {w_slab}",
        "",
        f"def E_ttp_hi_num : ℤ := {E_TTP_HI_NUM}",
        f"def E_ttp_hi_den : ℤ := {E_TTP_HI_DEN}",
        "",
        f"def e_int : ℤ := {e_int}",
        f"def ca_int : ℤ := {ca_int}",
        f"def cb_int : ℤ := {cb_int}",
        f"def cg_int : ℤ := {cg_int}",
        "",
        f"def hA_int : List ℤ := {fmt_list_int(hA_int)}",
        f"def hB_int : List ℤ := {fmt_list_int(hB_int)}",
        f"def hC_int : List ℤ := {fmt_list_int(hC_int)}",
        f"def psiBa_int : List ℤ := {fmt_list_int(psiBa_int)}",
        f"def psiCb_int : List ℤ := {fmt_list_int(psiCb_int)}",
        "",
        "def harmP : List CholHarmBlk := [",
        "  " + ",\n  ".join(fmt_harm_blk(k, m, c) for k, m, c in harmP),
        "]",
        "",
        "def harmR : List CholHarmBlk := [",
        "  " + ",\n  ".join(fmt_harm_blk(k, m, c) for k, m, c in harmR),
        "]",
        "",
    ]

    def emit_plain_list(list_name: str, items: list):
        names = []
        for name, mult, mp_p, bas, cols in items:
            vname = f"blk_{name}"
            names.append(vname)
            lines.append(f"def {vname} : CholPlainBlk := {fmt_plain_blk(mult, mp_p, bas, cols)}")
            lines.append("")
        lines.append(f"def {list_name} : List CholPlainBlk := [{', '.join(names)}]")
        lines.append("")

    def emit_std_list(list_name: str, items: list):
        names = []
        for name, mp_p, e1, e2, cols in items:
            vname = f"blk_{name}"
            names.append(vname)
            lines.append(f"def {vname} : CholStdBlk := {fmt_std_blk(mp_p, e1, e2, cols)}")
            lines.append("")
        lines.append(f"def {list_name} : List CholStdBlk := [{', '.join(names)}]")
        lines.append("")

    emit_plain_list("sosA_sym", sosA_sym)
    emit_plain_list("sosA_asym", sosA_asym)
    emit_plain_list("sosB_sym", sosB_sym)
    emit_plain_list("sosB_asym", sosB_asym)
    emit_plain_list("sosG_s3_plain", sosG_s3_plain)
    emit_std_list("sosG_s3_std", sosG_s3_std)
    emit_plain_list("sosG_s2", sosG_s2)

    lines += [
        f"def resA_int : Poly3 := {fmt_poly3(resA_p)}",
        f"def resB_int : Poly3 := {fmt_poly3(resB_p)}",
        f"def resG_int : Poly3 := {fmt_poly3(resG_p)}",
        "",
    ]
    for i in range(6):
        lines.append(f"def tauA_{i} : List (List ℤ) := {fmt_cols_1d(tauA[i])}")
    for i in range(4):
        lines.append(f"def sigB_{i} : List (List ℤ) := {fmt_cols_1d(sigB[i])}")
    for i in range(4):
        lines.append(f"def sigC_{i} : List (List ℤ) := {fmt_cols_1d(sigC[i])}")
    lines += [
        "",
        f"def res_yA_int : List ℤ := {fmt_list_int(res_yA)}",
        f"def res_yB_int : List ℤ := {fmt_list_int(res_yB)}",
        f"def res_yC_int : List ℤ := {fmt_list_int(res_yC)}",
        "",
        "/-! ## Kernel-Verified Certificate Checks -/",
        "",
        "def twoYH (h : List ℤ) : List ℤ :=",
        "  (h.zipIdx).foldl (fun acc ⟨c, d⟩ => padd acc (pscale (2 * c) (pmul [0, 1] (ppow [1, 0, -2] d)))) []",
        "",
        "def checkKronA : Bool :=",
        "  let eu := w_kron; let ev := w_kron * D_kron; let et := w_kron * D_kron * D_kron",
        "  let U : ℤ := ((Nat.shiftLeft 1 eu : ℕ) : ℤ)",
        "  let V : ℤ := ((Nat.shiftLeft 1 ev : ℕ) : ℤ)",
        "  let T : ℤ := ((Nat.shiftLeft 1 et : ℕ) : ℤ)",
        "  let gPu := harmListKevShift 0 eu eu harmP + harmListKevShift eu 0 eu harmP + harmListKevShift eu eu 0 harmP",
        "  let lhs := 40 * pevalZ hA_int U + 280 * (pevalZ psiBa_int V + pevalZ psiBa_int T) - 280 * ca_int",
        "    - 80 * gPu - 560 * (harmListKevShift eu ev et harmP + harmListKevShift eu et ev harmP)",
        "    - 560 * harmListKevShift ev et eu harmR",
        "  let rhs := sosA_sym.foldl (fun a b => a + cholPlainKevShift eu ev et b) 0",
        "    + sosA_asym.foldl (fun a b => a + cholPlainKevShift eu ev et b + cholPlainKevShift eu et ev b) 0",
        "    + kev3Shift eu ev et resA_int",
        "  lhs == rhs",
        "",
        "def checkKronB : Bool :=",
        "  let eu := w_kron; let ev := w_kron * D_kron; let et := w_kron * D_kron * D_kron",
        "  let U : ℤ := ((Nat.shiftLeft 1 eu : ℕ) : ℤ)",
        "  let V : ℤ := ((Nat.shiftLeft 1 ev : ℕ) : ℤ)",
        "  let T : ℤ := ((Nat.shiftLeft 1 et : ℕ) : ℤ)",
        "  let gPu := harmListKevShift 0 eu eu harmP + harmListKevShift eu 0 eu harmP + harmListKevShift eu eu 0 harmP",
        "  let gPv := harmListKevShift 0 ev ev harmP + harmListKevShift ev 0 ev harmP + harmListKevShift ev ev 0 harmP",
        "  let gRu := harmListKevShift 0 eu eu harmR + harmListKevShift eu 0 eu harmR + harmListKevShift eu eu 0 harmR",
        "  let gRv := harmListKevShift 0 ev ev harmR + harmListKevShift ev 0 ev harmR + harmListKevShift ev ev 0 harmR",
        "  let lhs := 2 * (pevalZ hB_int U - pevalZ psiBa_int U + pevalZ hB_int V - pevalZ psiBa_int V)",
        "    + 12 * pevalZ psiCb_int T - 12 * cb_int - 2 * (gPu + gPv + gRu + gRv)",
        "    - 24 * harmListKevShift eu ev et harmP",
        "    - 24 * (harmListKevShift eu et ev harmR + harmListKevShift ev et eu harmR)",
        "  let rhs := sosB_sym.foldl (fun a b => a + cholPlainKevShift eu ev et b) 0",
        "    + sosB_asym.foldl (fun a b => a + cholPlainKevShift eu ev et b + cholPlainKevShift ev eu et b) 0",
        "    + kev3Shift eu ev et resB_int",
        "  lhs == rhs",
        "",
        "def checkKronG : Bool :=",
        "  let eu := w_kron; let ev := w_kron * D_kron; let et := w_kron * D_kron * D_kron",
        "  let U : ℤ := ((Nat.shiftLeft 1 eu : ℕ) : ℤ)",
        "  let V : ℤ := ((Nat.shiftLeft 1 ev : ℕ) : ℤ)",
        "  let T : ℤ := ((Nat.shiftLeft 1 et : ℕ) : ℤ)",
        "  let gRu := harmListKevShift 0 eu eu harmR + harmListKevShift eu 0 eu harmR + harmListKevShift eu eu 0 harmR",
        "  let gRv := harmListKevShift 0 ev ev harmR + harmListKevShift ev 0 ev harmR + harmListKevShift ev ev 0 harmR",
        "  let gRt := harmListKevShift 0 et et harmR + harmListKevShift et 0 et harmR + harmListKevShift et et 0 harmR",
        "  let lhs := 252 * (pevalZ hC_int U - 2 * pevalZ psiCb_int U",
        "      + pevalZ hC_int V - 2 * pevalZ psiCb_int V",
        "      + pevalZ hC_int T - 2 * pevalZ psiCb_int T)",
        "    - 36 * cg_int - 504 * (gRu + gRv + gRt)",
        "    - 2520 * (harmListKevShift eu ev et harmR + harmListKevShift eu et ev harmR + harmListKevShift ev et eu harmR)",
        "  let rhs := sosG_s3_plain.foldl (fun a b => a + cholPlainKevShift eu ev et b) 0",
        "    + sosG_s3_std.foldl (fun a b => a + cholStdKev w_kron D_kron b) 0",
        "    + sosG_s2.foldl (fun a b => a + cholPlainKevShift eu ev et b + cholPlainKevShift ev eu et b + cholPlainKevShift et eu ev b) 0",
        "    + kev3Shift eu ev et resG_int",
        "  lhs == rhs",
        "",
        "def l1A : ℕ :=",
        "  40 * l1List hA_int + 280 * l1List psiBa_int + 280 * l1List psiBa_int + 280 * ca_int.natAbs",
        "  + 80 * (3 * harmListL1 harmP) + 560 * (2 * harmListL1 harmP) + 560 * harmListL1 harmR",
        "  + sosA_sym.foldl (fun a b => a + cholPlainL1 b) 0",
        "  + 2 * sosA_asym.foldl (fun a b => a + cholPlainL1 b) 0",
        "  + l1Poly3 resA_int",
        "",
        "def l1B : ℕ :=",
        "  2 * (l1List hB_int + l1List psiBa_int) + 2 * (l1List hB_int + l1List psiBa_int)",
        "  + 12 * l1List psiCb_int + 12 * cb_int.natAbs",
        "  + 2 * (3 * harmListL1 harmP + 3 * harmListL1 harmP + 3 * harmListL1 harmR + 3 * harmListL1 harmR)",
        "  + 24 * harmListL1 harmP + 24 * (2 * harmListL1 harmR)",
        "  + sosB_sym.foldl (fun a b => a + cholPlainL1 b) 0",
        "  + 2 * sosB_asym.foldl (fun a b => a + cholPlainL1 b) 0",
        "  + l1Poly3 resB_int",
        "",
        "def l1G : ℕ :=",
        "  252 * (l1List hC_int + 2 * l1List psiCb_int + l1List hC_int + 2 * l1List psiCb_int + l1List hC_int + 2 * l1List psiCb_int)",
        "  + 36 * cg_int.natAbs",
        "  + 504 * (3 * harmListL1 harmR + 3 * harmListL1 harmR + 3 * harmListL1 harmR)",
        "  + 2520 * (3 * harmListL1 harmR)",
        "  + sosG_s3_plain.foldl (fun a b => a + cholPlainL1 b) 0",
        "  + sosG_s3_std.foldl (fun a b => a + cholStdL1 b) 0",
        "  + 3 * sosG_s2.foldl (fun a b => a + cholPlainL1 b) 0",
        "  + l1Poly3 resG_int",
        "",
        "def plainDegOk (blk : CholPlainBlk) (dmp db : ℕ) : Bool :=",
        "  blk.mp.all (fun x => decide (x.2.1 ≤ dmp ∧ x.2.2.1 ≤ dmp ∧ x.2.2.2 ≤ dmp)) &&",
        "  blk.basis.toList.all (fun p => p.all (fun x => decide (x.2.1 ≤ db ∧ x.2.2.1 ≤ db ∧ x.2.2.2 ≤ db)))",
        "",
        "def stdDegOk (blk : CholStdBlk) (dmp db : ℕ) : Bool :=",
        "  blk.mp.all (fun x => decide (x.2.1 ≤ dmp ∧ x.2.2.1 ≤ dmp ∧ x.2.2.2 ≤ dmp)) &&",
        "  blk.e1.toList.all (fun p => p.all (fun x => decide (x.2.1 ≤ db ∧ x.2.2.1 ≤ db ∧ x.2.2.2 ≤ db))) &&",
        "  blk.e2.toList.all (fun p => p.all (fun x => decide (x.2.1 ≤ db ∧ x.2.2.1 ≤ db ∧ x.2.2.2 ≤ db)))",
        "",
        "def poly3DegOk (p : Poly3) (d : ℕ) : Bool :=",
        "  p.all (fun x => decide (x.2.1 ≤ d ∧ x.2.2.1 ≤ d ∧ x.2.2.2 ≤ d))",
        "",
        "def harmDegOk (blks : List CholHarmBlk) (M : ℕ) : Bool :=",
        "  blks.all (fun blk => decide (blk.k ≤ M) &&",
        "    blk.cols.toList.all (fun col => col.all (fun p => decide (blk.k + p.1 ≤ M))))",
        "",
        "theorem kronA_ok : checkKronA = true := by decide +kernel",
        "theorem kronB_ok : checkKronB = true := by decide +kernel",
        "theorem kronG_ok : checkKronG = true := by decide +kernel",
        "",
        "theorem l1_ok : l1A < 2 ^ w_kron ∧ l1B < 2 ^ w_kron ∧ l1G < 2 ^ w_kron := by decide +kernel",
        "",
        "theorem harm_deg_ok : harmDegOk harmP 5 = true ∧ harmDegOk harmR 5 = true := by decide +kernel",
        "",
        "theorem res_deg_ok :",
        "    poly3DegOk resA_int 11 = true ∧ poly3DegOk resB_int 11 = true ∧ poly3DegOk resG_int 11 = true := by",
        "  decide +kernel",
        "",
        "theorem sosA_deg_ok :",
        "    sosA_sym.all (fun b => plainDegOk b 2 5) = true ∧",
        "    sosA_asym.all (fun b => plainDegOk b 1 4) = true := by decide +kernel",
        "",
        "theorem sosB_deg_ok :",
        "    sosB_sym.all (fun b => plainDegOk b 2 5) = true ∧",
        "    sosB_asym.all (fun b => plainDegOk b 1 4) = true := by decide +kernel",
        "",
        "theorem sosG_deg_ok :",
        "    sosG_s3_plain.all (fun b => plainDegOk b 2 5) = true ∧",
        "    sosG_s3_std.all (fun b => stdDegOk b 2 5) = true ∧",
        "    sosG_s2.all (fun b => plainDegOk b 1 4) = true := by decide +kernel",
        "",
        "-- Wait: check actual tight degrees per block (1 has dmp=0,db=5 -> 10; u_lo/hi_u has dmp=1,db=4 -> 9; detG has dmp=2,db=3 -> 8)",
        "theorem sos_exact_deg_ok :",
        "    plainDegOk blk_SOS_A_1_even 0 5 = true ∧ plainDegOk blk_SOS_A_1_odd 0 5 = true ∧",
        "    plainDegOk blk_SOS_A_ulo_even 1 4 = true ∧ plainDegOk blk_SOS_A_ulo_odd 1 4 = true ∧",
        "    plainDegOk blk_SOS_A_hiu_even 1 4 = true ∧ plainDegOk blk_SOS_A_hiu_odd 1 4 = true ∧",
        "    plainDegOk blk_SOS_A_detG_even 2 3 = true ∧ plainDegOk blk_SOS_A_detG_odd 2 3 = true ∧",
        "    plainDegOk blk_SOS_A_vlo 1 4 = true ∧ plainDegOk blk_SOS_A_vhi 1 4 = true ∧",
        "    plainDegOk blk_SOS_B_1_even 0 5 = true ∧ plainDegOk blk_SOS_B_1_odd 0 5 = true ∧",
        "    plainDegOk blk_SOS_B_tlo_even 1 4 = true ∧ plainDegOk blk_SOS_B_tlo_odd 1 4 = true ∧",
        "    plainDegOk blk_SOS_B_thi_even 1 4 = true ∧ plainDegOk blk_SOS_B_thi_odd 1 4 = true ∧",
        "    plainDegOk blk_SOS_B_detG_even 2 3 = true ∧ plainDegOk blk_SOS_B_detG_odd 2 3 = true ∧",
        "    plainDegOk blk_SOS_B_ulo 1 4 = true ∧ plainDegOk blk_SOS_B_uhi 1 4 = true ∧",
        "    plainDegOk blk_SOS_G_1_triv 0 5 = true ∧ plainDegOk blk_SOS_G_1_sign 0 5 = true ∧",
        "    plainDegOk blk_SOS_G_detG_triv 2 3 = true ∧ plainDegOk blk_SOS_G_detG_sign 2 3 = true ∧",
        "    stdDegOk blk_SOS_G_1_std 0 5 = true ∧ stdDegOk blk_SOS_G_detG_std 2 3 = true ∧",
        "    plainDegOk blk_SOS_G_ulo_even 1 4 = true ∧ plainDegOk blk_SOS_G_ulo_odd 1 4 = true ∧",
        "    plainDegOk blk_SOS_G_uhi_even 1 4 = true ∧ plainDegOk blk_SOS_G_uhi_odd 1 4 = true := by",
        "  decide +kernel",
        "",
        "theorem norm_ok :",
        "    e_int + 2 * harmListKevShift 0 0 0 harmP + 7 * harmListKevShift 0 0 0 harmR =",
        "    7 * ca_int + 42 * cb_int + cg_int := by decide +kernel",
        "",
        "theorem minorA_ok :",
        "    (padd (pscale 20 (padd (twoYH hA_int) [-S2]))",
        "      (padd (pscale 20 (chol1DPoly tauA_0))",
        "      (padd (pmul [0, 20] (chol1DPoly tauA_1))",
        "      (padd (pmul [-19, 0, 20] (chol1DPoly tauA_2))",
        "      (padd (pmul [20, 0, -20] (chol1DPoly tauA_3))",
        "      (padd (pmul [0, -19, 0, 20] (chol1DPoly tauA_4))",
        "      (padd (pmul [0, 20, 0, -20] (chol1DPoly tauA_5))",
        "            (pneg res_yA_int)))))))).all (· == 0) = true := by decide +kernel",
        "",
        "theorem minorB_ok :",
        "    (padd (padd (twoYH hB_int) [-S2])",
        "      (padd (chol1DPoly sigB_0)",
        "      (padd (pmul [0, 1] (chol1DPoly sigB_1))",
        "      (padd (pmul [1, 0, -1] (chol1DPoly sigB_2))",
        "      (padd (pmul [0, 1, 0, -1] (chol1DPoly sigB_3))",
        "            (pneg res_yB_int)))))).all (· == 0) = true := by decide +kernel",
        "",
        "theorem minorC_ok :",
        "    (padd (padd (twoYH hC_int) [-S2])",
        "      (padd (chol1DPoly sigC_0)",
        "      (padd (pmul [0, 1] (chol1DPoly sigC_1))",
        "      (padd (pmul [1, 0, -1] (chol1DPoly sigC_2))",
        "      (padd (pmul [0, 1, 0, -1] (chol1DPoly sigC_3))",
        "            (pneg res_yC_int)))))).all (· == 0) = true := by decide +kernel",
        "",
        "theorem bound_ok :",
        "    let r1 : ℤ := 9 * (l1Poly3 resA_int : ℤ) + 1260 * (l1Poly3 resB_int : ℤ) + 10 * (l1Poly3 resG_int : ℤ)",
        "    let r2 : ℤ := max (l1List res_yA_int : ℤ) (max (20 * (l1List res_yB_int : ℤ)) (20 * (l1List res_yC_int : ℤ)))",
        "    E_ttp_hi_num * 18 * (20 * S2 + r2) < E_ttp_hi_den * (360 * e_int - r1) := by",
        "  decide +kernel",
        "",
        "end ThomsonN9.StageB.SlabCertData",
        "",
    ]

    out_path = LEAN_STAGEB / "SlabCertData.lean"
    out_path.write_text("\n".join(lines))
    print(f"  Wrote {out_path} ({out_path.stat().st_size / 1024:.1f} KB) in {time.time() - t0:.2f}s")


# ---------------------------------------------------------------------------
# PART 2: Exact Bernstein Certificate Builder for CapCert L3 Tube Forcing
# ---------------------------------------------------------------------------

def build_bernstein_piece(P: list[int], u1: int, u2: int, w1: int, w2: int, max_elev: int = 120):
    """Find (Lam, beta) with beta_i >= 0 such that Lam * P(y) == sum_i beta_i (u2*y - u1)^i (w1 - w2*y)^(n-i)."""
    n = len(P) - 1
    while n > 0 and P[n] == 0:
        n -= 1
    P = P[: n + 1]
    Delta = u2 * w1 - w2 * u1
    assert Delta > 0, f"Invalid interval [{u1}/{u2}, {w1}/{w2}]"

    # Represent homogeneous polynomials of degree d in (A, B) as list of length d+1: c[i] = coeff of A^i B^(d-i)
    def hmul(a: list[int], b: list[int]) -> list[int]:
        out = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        out[i + j] += x * y
        return out

    def hpow(base: list[int], k: int) -> list[int]:
        res = [1]
        for _ in range(k):
            res = hmul(res, base)
        return res

    # y * Delta = w1 * A + u1 * B -> [u1, w1]
    # 1 * Delta = w2 * A + u2 * B -> [u2, w2]
    Y_h = [u1, w1]
    O_h = [u2, w2]
    beta = [0] * (n + 1)
    for k, pk in enumerate(P):
        if pk == 0:
            continue
        term = hmul(hpow(Y_h, k), hpow(O_h, n - k))
        for i, v in enumerate(term):
            beta[i] += pk * v
    Lam = Delta ** n

    # Elevate degree by multiplying by O_h = (w2*A + u2*B) = Delta until all beta[i] >= 0
    elev = 0
    while min(beta) < 0:
        elev += 1
        if elev > max_elev:
            raise RuntimeError(
                f"Bernstein elevation failed on [{u1}/{u2}, {w1}/{w2}] after {max_elev} steps; "
                f"min={min(beta)}, max={max(beta)}"
            )
        beta = hmul(beta, O_h)
        Lam *= Delta

    # Reduce by exact GCD to keep integers as small as possible
    g = Lam
    for b in beta:
        g = math.gcd(g, b)
    if g > 1:
        Lam //= g
        beta = [b // g for b in beta]

    # Exact verification against PolyKron's bernSum definition!
    a_poly = [-u1, u2]
    b_poly = [w1, -w2]
    deg_tot = len(beta) - 1
    acc = [0]
    pow_a = [[1]]
    pow_b = [[1]]
    for _ in range(deg_tot):
        pow_a.append(pmul_1d(pow_a[-1], a_poly))
        pow_b.append(pmul_1d(pow_b[-1], b_poly))
    for i, bi in enumerate(beta):
        if bi:
            acc = padd_1d(acc, pscale_1d(bi, pmul_1d(pow_a[i], pow_b[deg_tot - i])))
    lhs = pscale_1d(Lam, P)
    diff = padd_1d(lhs, pscale_1d(-1, acc))
    assert all(x == 0 for x in diff), f"Bernstein identity check failed on [{u1}/{u2}, {w1}/{w2}]!"
    return dict(u1=u1, u2=u2, w1=w1, w2=w2, Lam=Lam, beta=beta, elev=elev)


# ---------------------------------------------------------------------------
# PART 3: Export CapCertHarmData.lean, CapCertSosData.lean, CapCertBernData.lean
# ---------------------------------------------------------------------------

def export_cap(B: int = 76, D_kron: int = 20):
    t0 = time.time()
    print(f"\n=== Exporting CapCert*Data.lean (B={B}, D={D_kron}) ===")
    cap_path = REPO / "certificates" / "n9-stage-a-r24-symcap-m090_M10K10.json"
    raw = json.loads(cap_path.read_text())
    a0 = Fraction(raw["a0"])
    M, K = int(raw["M"]), int(raw["K"])
    assert a0 == Fraction(-9, 10) and M == 10 and K == 10
    model = SymCapModel(9, a0, M, K)

    S2 = 1 << (2 * B)
    rS2 = lambda q: int(round(q * S2))
    e_int = math.floor(Fraction(raw["e"]) * S2)
    H_int = [rS2(Fraction(x)) for x in raw["h"]]

    bj_map = {b["name"]: b for b in raw["blocks"]}
    spec_map = {b["name"]: b for b in model.blocks}

    harmBlks = []
    for k in range(K):
        name = f"F_{k}"
        cols_sp, _, _ = cholesky_cols_int(load_utri_matrix(bj_map[name]), B)
        harmBlks.append((k, M - k, cols_sp))

    s_dict = harm_list_to_dict(model.Q, harmBlks)
    s111_int = sum(s_dict.values())
    assert s111_int == harm_list_kev_shift(0, 0, 0, harmBlks)
    g_int = eval_g_int_dict(s_dict)

    def mk_plain(name: str, mult: int, mp_scale: int, basis_scale: int):
        spec = spec_map[name]
        cols_sp, _, _ = cholesky_cols_int(load_utri_matrix(bj_map[name]), B)
        mp_p = scale_poly_to_int(spec["mp"], mp_scale)
        basis_p = [scale_poly_to_int(b, basis_scale) for b in spec["basis"]]
        return (name, mult, mp_p, basis_p, cols_sp)

    def mk_std(name: str, mp_mult: int, basis_scale: int):
        spec = spec_map[name]
        cols_sp, _, _ = cholesky_cols_int(load_utri_matrix(bj_map[name]), B)
        mp_p = scale_poly_to_int(spec["mp"], mp_mult)
        e1_p = [scale_poly_to_int(pair[0], basis_scale) for pair in spec["basis"]]
        e2_p = [scale_poly_to_int(pair[1], basis_scale) for pair in spec["basis"]]
        return (name, mp_p, e1_p, e2_p, cols_sp)

    # K_cap = 360
    sos_plain_s3 = [
        mk_plain("SOS_1_triv", 10, 1, 6),
        mk_plain("SOS_1_sign", 10, 1, 6),
        mk_plain("SOS_detG_triv", 10, 1, 6),
        mk_plain("SOS_detG_sign", 10, 1, 6),
    ]
    sos_std_s3 = [
        mk_std("SOS_1_std", 30, 2),
        mk_std("SOS_detG_std", 30, 2),
    ]
    sos_ulo = [
        mk_plain("SOS_ulo_even", 3, 10, 2),
        mk_plain("SOS_ulo_odd", 3, 10, 2),
    ]
    sos_uhi = [
        mk_plain("SOS_uhi_even", 30, 1, 2),
        mk_plain("SOS_uhi_odd", 30, 1, 2),
    ]

    # 360 * S^2 * slack(u, v, t):
    #   = 120*(H(u)+H(v)+H(t)) - 10*e_int - 840*(s(u,v,t) + s(u,t,v) + s(v,t,u))
    #     - 120*(g(u)+g(v)+g(t)) - 45*s(1,1,1)
    slack_d: dict = {}
    for var in (0, 1, 2):
        slack_d = dict_add(slack_d, list_1d_to_dict(H_int, var), 120)
        slack_d = dict_add(slack_d, list_1d_to_dict(g_int, var), -120)
    slack_d = dict_add(slack_d, {(0, 0, 0): -10 * e_int - 45 * s111_int}, 1)
    slack_d = dict_add(slack_d, s_dict, -840)
    slack_d = dict_add(slack_d, dict_perm(s_dict, (0, 2, 1)), -840)
    slack_d = dict_add(slack_d, dict_perm(s_dict, (1, 2, 0)), -840)

    sos_d: dict = {}
    for _, mult, mp_p, bas, cols in sos_plain_s3:
        sos_d = dict_add(sos_d, plain_blk_to_dict(mult, mp_p, bas, cols))
    for _, mp_p, e1, e2, cols in sos_std_s3:
        sos_d = dict_add(sos_d, std_blk_to_dict(mp_p, e1, e2, cols))
    for _, mult, mp_p, bas, cols in sos_ulo + sos_uhi:
        bd = plain_blk_to_dict(mult, mp_p, bas, cols)
        sos_d = dict_add(sos_d, bd)
        sos_d = dict_add(sos_d, dict_perm(bd, (1, 0, 2)))
        sos_d = dict_add(sos_d, dict_perm(bd, (2, 0, 1)))
    res_slack_p = dict_to_poly3(dict_add(slack_d, sos_d, -1))

    # 1D minorant (b^2 = 19/20, multiply by 20 * S^2)
    sig = [cholesky_cols_int(load_utri_matrix(bj_map[f"sig_{i}"]), B)[1] for i in range(4)]
    res_y = padd_1d(pscale_1d(20, padd_1d(two_y_H_1m2y2(H_int), [-S2])),
            padd_1d(pscale_1d(20, chol1d_poly(sig[0])),
            padd_1d(pmul_1d([0, 20], chol1d_poly(sig[1])),
            padd_1d(pmul_1d([19, 0, -20], chol1d_poly(sig[2])),
                    pmul_1d([0, 19, 0, -20], chol1d_poly(sig[3]))))))
    while res_y and res_y[-1] == 0:
        res_y.pop()

    l1_l = lambda lst: sum(abs(x) for x in lst)
    l1_p3 = lambda p: sum(abs(c) for c, _, _, _ in p)
    l1_h = harm_list_l1(harmBlks)
    L1_cap = (3 * 120 * l1_l(H_int) + 10 * abs(e_int) + 45 * abs(s111_int)
              + 3 * 120 * 3 * l1_h + 840 * 3 * l1_h
              + sum(chol_plain_l1(m, mp_p, b, c) for _, m, mp_p, b, c in sos_plain_s3)
              + sum(chol_std_l1(mp_p, e1, e2, c) for _, mp_p, e1, e2, c in sos_std_s3)
              + 3 * sum(chol_plain_l1(m, mp_p, b, c) for _, m, mp_p, b, c in sos_ulo + sos_uhi)
              + l1_p3(res_slack_p))
    w_cap = L1_cap.bit_length() + 4

    # Pre-verify Kronecker identity == 0!
    eu, ev, et = w_cap, w_cap * D_kron, w_cap * D_kron * D_kron
    U, V, T = 1 << eu, 1 << ev, 1 << et
    g_u = harm_list_kev_shift(0, eu, eu, harmBlks) + harm_list_kev_shift(eu, 0, eu, harmBlks) + harm_list_kev_shift(eu, eu, 0, harmBlks)
    g_v = harm_list_kev_shift(0, ev, ev, harmBlks) + harm_list_kev_shift(ev, 0, ev, harmBlks) + harm_list_kev_shift(ev, ev, 0, harmBlks)
    g_t = harm_list_kev_shift(0, et, et, harmBlks) + harm_list_kev_shift(et, 0, et, harmBlks) + harm_list_kev_shift(et, et, 0, harmBlks)
    lhs = (120 * (pevalZ(H_int, U) + pevalZ(H_int, V) + pevalZ(H_int, T))
           - 10 * e_int - 45 * s111_int
           - 120 * (g_u + g_v + g_t)
           - 840 * (harm_list_kev_shift(eu, ev, et, harmBlks)
                    + harm_list_kev_shift(eu, et, ev, harmBlks)
                    + harm_list_kev_shift(ev, et, eu, harmBlks)))
    rhs = (sum(chol_plain_kev_shift(eu, ev, et, m, mp_p, b, c) for _, m, mp_p, b, c in sos_plain_s3)
           + sum(chol_std_kev(w_cap, D_kron, mp_p, e1, e2, c) for _, mp_p, e1, e2, c in sos_std_s3)
           + sum(chol_plain_kev_shift(eu, ev, et, m, mp_p, b, c)
                 + chol_plain_kev_shift(ev, eu, et, m, mp_p, b, c)
                 + chol_plain_kev_shift(et, eu, ev, m, mp_p, b, c)
                 for _, m, mp_p, b, c in sos_ulo + sos_uhi)
           + kev3_shift(eu, ev, et, res_slack_p))
    assert lhs == rhs, "CAP KRONECKER CHECK FAILED!"

    R1 = Fraction(l1_p3(res_slack_p), 360 * S2)
    R2 = Fraction(l1_l(res_y), 20 * S2)
    e_frac = Fraction(e_int, S2)
    Delta_cap = (1 + R2) * E_TTP_HI - (e_frac - 36 * R1)
    rhs_y_bound = 2 * Delta_cap - R2  # upper bound on 1 - 2y*H(1-2y^2) for every pair!
    eps_y_num = 1
    eps_y_den = 2 * (10 ** 14)  # 5e-15
    eps_y = Fraction(eps_y_num, eps_y_den)
    assert rhs_y_bound < eps_y, f"2*Delta_cap - R2 = {float(rhs_y_bound):.3e} >= eps_y = {float(eps_y):.3e}!"
    print(f"  [OK] Pre-verified CAP Kron == 0 (w={w_cap}, D={D_kron})")
    print(f"       R1={float(R1):.2e}, R2={float(R2):.2e}, 2*Delta_cap-R2={float(rhs_y_bound):.3e} < eps_y={float(eps_y):.3e}")

    # Build 7 Bernstein pieces for Peps(y) = eps_y_den * S^2 * ((1 - eps_y) - 2y * H(1 - 2y^2))
    # = (eps_y_den - eps_y_num) * S^2 - eps_y_den * two_y_H_1m2y2(H_int)
    # Wait: simplify gcd with S^2! Note eps_y_den = 2 * 10^14 = 2^15 * 5^14.
    # Let's divide (eps_y_den * S^2) by gcd(eps_y_den, 1) -> just keep K_bern = 5^14 (since 2^15 divides S^2)!
    # Check: (1 - 1/(2*10^14)) * S^2 = S^2 - S^2 / (2^15 * 5^14), so multiply by 5^14:
    # Peps(y) = 5^14 * S^2 - (S^2 // 2^15) - 5^14 * two_y_H_1m2y2(H_int)
    # WAIT: check! Peps(y) / (5^14 * S^2) = 1 - 1/(2^15 * 5^14) - 2y * H(1-2y^2) = (1 - eps_y) - 2y * H(1-2y^2)!!
    assert S2 % (1 << 15) == 0
    K_bern = 5 ** 14
    const_peps = K_bern * S2 - (S2 >> 15)
    Peps = padd_1d([const_peps], pscale_1d(-K_bern, two_y_H_1m2y2(H_int)))
    # Verify exact scaling: Peps(y) / (K_bern * S2) == (1 - eps_y) - 2y * H(1 - 2y^2)
    assert Fraction(const_peps, K_bern * S2) == 1 - eps_y

    # Choose clean 5-digit (denominator 10^5) rational y-tube endpoints [y_a_lo, y_a_hi] for a = 0..5
    # Recall nu_0 < nu_1 < nu_2 < nu_3 < nu_4 < nu_5, so y_a = sqrt((1 - nu_a)/2) is DECREASING in a:
    #   y_5 < y_4 < y_3 < y_2 < y_1 < y_0!
    # Requirement: for EVERY y in [y_a_lo, y_a_hi], t = 1 - 2*y^2 satisfies:
    #   nuHi_a - 1/10000 <= t <= nuLo_a + 1/10000
    # so for ANY z in [zLo, zHi] (where nuLo_a <= nu_a(z) <= nuHi_a):
    #   |t - nu_a(z)| <= 1/10000!
    # i.e. 1 - 2*y_a_lo^2 <= nuLo_a + 1/10000  (so y_a_lo >= sqrt((1 - nuLo_a - 1/10000)/2))
    #  and 1 - 2*y_a_hi^2 >= nuHi_a - 1/10000  (so y_a_hi <= sqrt((1 - nuHi_a + 1/10000)/2))
    rho = Fraction(1, 10000)
    y_tubes = []  # indexed by a = 0..5
    D_end = 100000
    for a, (nulo, nuhi) in enumerate(NU_CONTAINERS):
        t_max = nulo + rho
        t_min = nuhi - rho
        y_lo_min = math.sqrt(float((1 - t_max) / 2))
        y_hi_max = math.sqrt(float((1 - t_min) / 2))
        # Pick interior rationals with denominator D_end (with tiny inward margin so strict ineq holds cleanly!)
        ylo_n = math.ceil(y_lo_min * D_end)
        while 1 - 2 * Fraction(ylo_n, D_end) ** 2 > t_max:
            ylo_n += 1
        yhi_n = math.floor(y_hi_max * D_end)
        while 1 - 2 * Fraction(yhi_n, D_end) ** 2 < t_min:
            yhi_n -= 1
        ylo = Fraction(ylo_n, D_end)
        yhi = Fraction(yhi_n, D_end)
        assert ylo < yhi
        assert 1 - 2 * ylo ** 2 <= nulo + rho
        assert nuhi - rho <= 1 - 2 * yhi ** 2
        y_tubes.append((ylo, yhi))
        print(f"  Tube a={a}: y in [{ylo}, {yhi}]  (t in [{float(1-2*yhi**2):+.6f}, {float(1-2*ylo**2):+.6f}])")

    # Sort tubes in increasing y order: a = 5, 4, 3, 2, 1, 0
    # Complement of 6 tubes inside [0, 9747/10000] = 7 segments:
    y_top = Fraction(9747, 10000)
    assert y_top ** 2 > Fraction(19, 20)
    segs = [
        (Fraction(0, 1), y_tubes[5][0]),
        (y_tubes[5][1], y_tubes[4][0]),
        (y_tubes[4][1], y_tubes[3][0]),
        (y_tubes[3][1], y_tubes[2][0]),
        (y_tubes[2][1], y_tubes[1][0]),
        (y_tubes[1][1], y_tubes[0][0]),
        (y_tubes[0][1], y_top),
    ]
    bpieces = []
    for idx, (u, w) in enumerate(segs):
        assert u < w
        bp = build_bernstein_piece(Peps, u.numerator, u.denominator, w.numerator, w.denominator, max_elev=200)
        bpieces.append(bp)
        print(f"  [OK] BPiece {idx} on [{u}, {w}]: deg={len(bp['beta'])-1} (elev={bp['elev']}), Lam_bits={bp['Lam'].bit_length()}")

    # Check exact integer bound for 2*Delta_cap - R2 < eps_y:
    # Delta_cap = (1 + R2) * E_TTP_HI - (e_frac - 36 * R1)
    # 2*Delta_cap - R2 = 2*E_TTP_HI + (2*E_TTP_HI - 1)*R2 - 2*e_frac + 72*R1 < eps_y
    # Here R1 = l1(res_slack) / (360 * S2), so 72 * R1 = l1(res_slack) / (5 * S2)
    # and R2 = l1(res_y) / (20 * S2).
    # Multiply by 20 * S2 * E_TTP_HI_DEN * eps_y_den:
    # Wait: even simpler, multiply by 20 * S2 * E_TTP_HI_DEN * 200000000000000
    # Check: E_TTP_HI_DEN = 10^16, eps_y_den = 2 * 10^14, lcm = 10^16! (eps_y = 50 / 10^16!)
    assert E_TTP_HI_DEN % eps_y_den == 0
    eps_in_E_den = E_TTP_HI_DEN // eps_y_den  # = 50!
    r1_l1 = l1_p3(res_slack_p)
    r2_l1 = l1_l(res_y)
    # Multiply (2*E_TTP_HI + (2*E_TTP_HI - 1)*R2 - 2*e_frac + 72*R1 < eps_y) by 20 * S2 * E_TTP_HI_DEN:
    # 20 * (2 * E_TTP_HI_NUM * S2) + (2 * E_TTP_HI_NUM - E_TTP_HI_DEN) * r2_l1
    #   - 40 * e_int * E_TTP_HI_DEN + 4 * r1_l1 * E_TTP_HI_DEN < 20 * S2 * eps_in_E_den
    lhs_eps = (40 * E_TTP_HI_NUM * S2 + (2 * E_TTP_HI_NUM - E_TTP_HI_DEN) * r2_l1
               - 40 * e_int * E_TTP_HI_DEN + 4 * r1_l1 * E_TTP_HI_DEN)
    rhs_eps = 20 * S2 * eps_in_E_den
    assert lhs_eps < rhs_eps, f"Exact integer eps_y bound failed!"
    print(f"  [OK] Exact integer eps_y gap margin ratio: {rhs_eps / lhs_eps:.2f}x")

    # ---- Emit File 1: CapCertHarmData.lean ----
    harm_lines = [
        "import ThomsonN9.StageB.PolyKron",
        "",
        "/-!",
        "# Thomson N = 9 Stage B — Cap Certificate Harmonic & 1D Minorant Data (`[-9/10, 1]`, `M=10, K=10`)",
        "",
        "Auto-generated by `numerics/bounds/export_lean_stage_b.py` from",
        "`certificates/n9-stage-a-r24-symcap-m090_M10K10.json`.",
        "-/",
        "",
        "set_option maxHeartbeats 8000000",
        "set_option maxRecDepth 200000",
        "",
        "namespace ThomsonN9.StageB.CapCertHarmData",
        "",
        "open ThomsonN9.StageB.PolyKron",
        "",
        f"def B_bits : ℕ := {B}",
        f"def S2 : ℤ := {S2}",
        f"def D_kron : ℕ := {D_kron}",
        f"def w_kron : ℕ := {w_cap}",
        "",
        f"def E_ttp_hi_num : ℤ := {E_TTP_HI_NUM}",
        f"def E_ttp_hi_den : ℤ := {E_TTP_HI_DEN}",
        f"def eps_y_num : ℤ := {eps_y_num}",
        f"def eps_y_den : ℤ := {eps_y_den}",
        f"def K_bern : ℤ := {K_bern}",
        "",
        f"def e_int : ℤ := {e_int}",
        f"def H_int : List ℤ := {fmt_list_int(H_int)}",
        "",
        "def harmBlks : List CholHarmBlk := [",
        "  " + ",\n  ".join(fmt_harm_blk(k, m, c) for k, m, c in harmBlks),
        "]",
        "",
    ]
    for i in range(4):
        harm_lines.append(f"def sig_{i} : List (List ℤ) := {fmt_cols_1d(sig[i])}")
    harm_lines += [
        "",
        f"def res_y_int : List ℤ := {fmt_list_int(res_y)}",
        "",
        "def twoYH (h : List ℤ) : List ℤ :=",
        "  (h.zipIdx).foldl (fun acc ⟨c, d⟩ => padd acc (pscale (2 * c) (pmul [0, 1] (ppow [1, 0, -2] d)))) []",
        "",
        "def harmDegOk (blks : List CholHarmBlk) (M : ℕ) : Bool :=",
        "  blks.all (fun blk => decide (blk.k ≤ M) &&",
        "    blk.cols.toList.all (fun col => col.all (fun p => decide (blk.k + p.1 ≤ M))))",
        "",
        "theorem harm_deg_ok : harmDegOk harmBlks 9 = true := by decide +kernel",
        "",
        "theorem minor_ok :",
        "    (padd (pscale 20 (padd (twoYH H_int) [-S2]))",
        "      (padd (pscale 20 (chol1DPoly sig_0))",
        "      (padd (pmul [0, 20] (chol1DPoly sig_1))",
        "      (padd (pmul [19, 0, -20] (chol1DPoly sig_2))",
        "      (padd (pmul [0, 19, 0, -20] (chol1DPoly sig_3))",
        "            (pneg res_y_int)))))).all (· == 0) = true := by decide +kernel",
        "",
        "end ThomsonN9.StageB.CapCertHarmData",
        "",
    ]
    p_harm = LEAN_STAGEB / "CapCertHarmData.lean"
    p_harm.write_text("\n".join(harm_lines))
    print(f"  Wrote {p_harm} ({p_harm.stat().st_size / 1024:.1f} KB)")

    # ---- Emit File 2: CapCertSosData.lean (zero-MVar chunked + 2D-Kronecker slices) ----
    def fmt_raw_int(n: int) -> str:
        return f"Int.ofNat {n}" if n >= 0 else f"Int.negSucc {-n - 1}"

    def fmt_raw_poly3(p: list) -> str:
        return "[" + ", ".join(f"({fmt_raw_int(c)}, {a}, {b}, {d})" for c, a, b, d in p) + "]"

    def fmt_raw_col(col: list) -> str:
        return "[" + ", ".join(f"({i}, {fmt_raw_int(c)})" for i, c in col) + "]"

    sos_lines = [
        "import ThomsonN9.StageB.CapCertHarmData",
        "import ThomsonN9.StageB.PolyKronFast",
        "",
        "/-!",
        "# Thomson N = 9 Stage B — Cap Certificate 3D SOS Data & 2D-Kronecker Setup (`M=10, K=10`)",
        "",
        "Auto-generated by `numerics/bounds/export_lean_stage_b.py`.",
        "-/",
        "",
        "set_option maxHeartbeats 16000000",
        "set_option maxRecDepth 200000",
        "",
        "namespace ThomsonN9.StageB.CapCertSosData",
        "",
        "open ThomsonN9.StageB.PolyKron",
        "open ThomsonN9.StageB.PolyKronFast",
        "open ThomsonN9.StageB.CapCertHarmData",
        "",
    ]

    def emit_plain_sos(list_name: str, items: list):
        names = []
        for name, mult, mp_p, bas, cols in items:
            vname = f"blk_{name}"
            names.append(vname)
            cnames = []
            for ci, col in enumerate(cols):
                cn = f"{vname}_c{ci}"
                cnames.append(cn)
                sos_lines.append(f"private def {cn} : List (ℕ × ℤ) := {fmt_raw_col(col)}")
            sos_lines.append(f"def {vname} : CholPlainBlk := {{")
            sos_lines.append(f"  mult := {mult},")
            sos_lines.append(f"  mp := {fmt_raw_poly3(mp_p)},")
            sos_lines.append("  basis := #[")
            sos_lines.append(",\n".join(f"    {fmt_raw_poly3(b)}" for b in bas))
            sos_lines.append("  ],")
            sos_lines.append(f"  cols := #[{', '.join(cnames)}]")
            sos_lines.append("}")
            sos_lines.append("")
        sos_lines.append(f"def {list_name} : List CholPlainBlk := [{', '.join(names)}]")
        sos_lines.append("")

    def emit_std_sos(list_name: str, items: list):
        names = []
        for name, mp_p, e1, e2, cols in items:
            vname = f"blk_{name}"
            names.append(vname)
            cnames = []
            for ci, col in enumerate(cols):
                cn = f"{vname}_c{ci}"
                cnames.append(cn)
                sos_lines.append(f"private def {cn} : List (ℕ × ℤ) := {fmt_raw_col(col)}")
            sos_lines.append(f"def {vname} : CholStdBlk := {{")
            sos_lines.append(f"  mp := {fmt_raw_poly3(mp_p)},")
            sos_lines.append("  e1 := #[")
            sos_lines.append(",\n".join(f"    {fmt_raw_poly3(b)}" for b in e1))
            sos_lines.append("  ],")
            sos_lines.append("  e2 := #[")
            sos_lines.append(",\n".join(f"    {fmt_raw_poly3(b)}" for b in e2))
            sos_lines.append("  ],")
            sos_lines.append(f"  cols := #[{', '.join(cnames)}]")
            sos_lines.append("}")
            sos_lines.append("")
        sos_lines.append(f"def {list_name} : List CholStdBlk := [{', '.join(names)}]")
        sos_lines.append("")

    emit_plain_sos("sos_plain_s3", sos_plain_s3)
    emit_std_sos("sos_std_s3", sos_std_s3)
    emit_plain_sos("sos_ulo", sos_ulo)
    emit_plain_sos("sos_uhi", sos_uhi)

    chunk_sz = 100
    ch_names = []
    for ci in range(0, len(res_slack_p), chunk_sz):
        cn = f"res_slack_ch{ci // chunk_sz}"
        ch_names.append(cn)
        sos_lines.append(f"private def {cn} : Poly3 := {fmt_raw_poly3(res_slack_p[ci:ci + chunk_sz])}")
    sos_lines.append(f"def res_slack_int : Poly3 := {' ++ '.join(ch_names)}")
    sos_lines += [
        "",
        "def D2_kron : ℕ := 19",
        "",
        "def wForT (T : ℤ) : ℕ :=",
        "  match T.natAbs with",
        f"  | 0 | 1 => {w_cap}",
        f"  | 2 => {w_cap + 18}",
        f"  | 3 => {w_cap + 29}",
        f"  | 4 => {w_cap + 36}",
        f"  | 5 => {w_cap + 42}",
        f"  | 6 => {w_cap + 47}",
        f"  | 7 => {w_cap + 51}",
        f"  | 8 => {w_cap + 54}",
        f"  | _ => {w_cap + 58}",
        "",
        "/-- Fast 2D-Kronecker exact integer identity check at slice `t = T` (`u = 2^w, v = 2^(w*19)`). -/",
        "def checkKronCapAtT (w : ℕ) (T : ℤ) : Bool :=",
        "  let eu := w; let ev := w * D2_kron",
        "  let U : ℤ := ((Nat.shiftLeft 1 eu : ℕ) : ℤ)",
        "  let V : ℤ := ((Nat.shiftLeft 1 ev : ℕ) : ℤ)",
        "  let s111 := harmListKevShift 0 0 0 harmBlks",
        "  let gu := harmListKevShift 0 eu eu harmBlks + harmListKevShift eu 0 eu harmBlks + harmListKevShift eu eu 0 harmBlks",
        "  let gv := harmListKevShift 0 ev ev harmBlks + harmListKevShift ev 0 ev harmBlks + harmListKevShift ev ev 0 harmBlks",
        "  let gt := harmListEvZ 1 T T harmBlks + harmListEvZ T 1 T harmBlks + harmListEvZ T T 1 harmBlks",
        "  let lhs := 120 * (pevalZ H_int U + pevalZ H_int V + pevalZ H_int T)",
        "    - 10 * e_int - 45 * s111 - 120 * (gu + gv + gt)",
        "    - 840 * (harmListKev2T eu ev T harmBlks + harmListKev2T_utv eu ev T harmBlks + harmListKev2T_utv ev eu T harmBlks)",
        "  let rhs := sos_plain_s3.foldl (fun a b => a + cholPlainKev2T eu ev T b) 0",
        "    + sos_std_s3.foldl (fun a b => a + cholStdKev2T eu ev T b) 0",
        "    + sos_ulo.foldl (fun a b => a + cholPlainKev2T eu ev T b + cholPlainKev2T ev eu T b + cholPlainKev2T_tuv eu ev T b) 0",
        "    + sos_uhi.foldl (fun a b => a + cholPlainKev2T eu ev T b + cholPlainKev2T ev eu T b + cholPlainKev2T_tuv eu ev T b) 0",
        "    + kev2T eu ev T res_slack_int",
        "  lhs == rhs",
        "",
        "def l1CapFast : ℕ :=",
        "  120 * (l1List H_int + l1List H_int + l1List H_int)",
        "  + 10 * e_int.natAbs + 45 * (harmListKevShift 0 0 0 harmBlks).natAbs",
        "  + 120 * (3 * harmListL1 harmBlks + 3 * harmListL1 harmBlks + 3 * harmListL1 harmBlks)",
        "  + 840 * (3 * harmListL1 harmBlks)",
        "  + sos_plain_s3.foldl (fun a b => a + cholPlainL1Fast 6 b) 0",
        "  + sos_std_s3.foldl (fun a b => a + cholStdL1Fast 8 4 b) 0",
        "  + 3 * sos_ulo.foldl (fun a b => a + cholPlainL1Fast 2 b) 0",
        "  + 3 * sos_uhi.foldl (fun a b => a + cholPlainL1Fast 2 b) 0",
        "  + l1Poly3 res_slack_int",
        "",
        "def plainDegOk (blk : CholPlainBlk) (dmp db : ℕ) : Bool :=",
        "  blk.mp.all (fun x => decide (x.2.1 ≤ dmp ∧ x.2.2.1 ≤ dmp ∧ x.2.2.2 ≤ dmp)) &&",
        "  blk.basis.toList.all (fun p => p.all (fun x => decide (x.2.1 ≤ db ∧ x.2.2.1 ≤ db ∧ x.2.2.2 ≤ db)))",
        "",
        "def stdDegOk (blk : CholStdBlk) (dmp db : ℕ) : Bool :=",
        "  blk.mp.all (fun x => decide (x.2.1 ≤ dmp ∧ x.2.2.1 ≤ dmp ∧ x.2.2.2 ≤ dmp)) &&",
        "  blk.e1.toList.all (fun p => p.all (fun x => decide (x.2.1 ≤ db ∧ x.2.2.1 ≤ db ∧ x.2.2.2 ≤ db))) &&",
        "  blk.e2.toList.all (fun p => p.all (fun x => decide (x.2.1 ≤ db ∧ x.2.2.1 ≤ db ∧ x.2.2.2 ≤ db)))",
        "",
        "def poly3DegOk (p : Poly3) (d : ℕ) : Bool :=",
        "  p.all (fun x => decide (x.2.1 ≤ d ∧ x.2.2.1 ≤ d ∧ x.2.2.2 ≤ d))",
        "",
        "theorem l1_fast_ok : l1CapFast < 2 ^ w_kron := by decide +kernel",
        "theorem basis_l1_ok :",
        "    sos_plain_s3.all (fun b => b.basis.toList.all (fun p => decide (l1Poly3 p ≤ 6))) = true ∧",
        "    sos_std_s3.all (fun b => b.e1.toList.all (fun p => decide (l1Poly3 p ≤ 8)) &&",
        "                             b.e2.toList.all (fun p => decide (l1Poly3 p ≤ 4))) = true ∧",
        "    sos_ulo.all (fun b => b.basis.toList.all (fun p => decide (l1Poly3 p ≤ 2))) = true ∧",
        "    sos_uhi.all (fun b => b.basis.toList.all (fun p => decide (l1Poly3 p ≤ 2))) = true := by decide +kernel",
        "theorem res_deg_ok : poly3DegOk res_slack_int 18 = true := by decide +kernel",
        "",
        "theorem basis_len_ok :",
        "    sos_plain_s3.all (fun b => decide (b.basis.size ≤ 256)) = true ∧",
        "    sos_std_s3.all (fun b => decide (b.e1.size ≤ 256 ∧ b.e2.size ≤ 256)) = true ∧",
        "    sos_ulo.all (fun b => decide (b.basis.size ≤ 256)) = true ∧",
        "    sos_uhi.all (fun b => decide (b.basis.size ≤ 256)) = true := by decide +kernel",
        "",
        "theorem l1_slices_ok :",
        "    ∀ T ∈ ([-9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List ℤ),",
        "      l1CapFast * (max 1 T.natAbs) ^ 18 < 2 ^ (wForT T) := by",
        f"  have h1 : l1CapFast < 2 ^ {w_cap} := l1_fast_ok",
        "  have h2 : ∀ T ∈ ([-9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List ℤ),",
        f"      2 ^ {w_cap} * (max 1 T.natAbs) ^ 18 ≤ 2 ^ (wForT T) := by decide",
        "  intro T hT",
        "  have hm : 0 < (max 1 T.natAbs) ^ 18 := Nat.pow_pos (by omega)",
        "  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h1 hm) (h2 T hT)",
        "",
        "theorem sos_exact_deg_ok :",
        "    plainDegOk blk_SOS_1_triv 0 9 = true ∧ plainDegOk blk_SOS_1_sign 0 9 = true ∧",
        "    plainDegOk blk_SOS_detG_triv 2 7 = true ∧ plainDegOk blk_SOS_detG_sign 2 7 = true ∧",
        "    stdDegOk blk_SOS_1_std 0 9 = true ∧ stdDegOk blk_SOS_detG_std 2 7 = true ∧",
        "    plainDegOk blk_SOS_ulo_even 1 8 = true ∧ plainDegOk blk_SOS_ulo_odd 1 8 = true ∧",
        "    plainDegOk blk_SOS_uhi_even 1 8 = true ∧ plainDegOk blk_SOS_uhi_odd 1 8 = true := by",
        "  decide +kernel",
        "",
        "theorem eps_gap_ok :",
        f"    40 * E_ttp_hi_num * S2 + (2 * E_ttp_hi_num - E_ttp_hi_den) * (l1List res_y_int : ℤ)",
        f"      - 40 * e_int * E_ttp_hi_den + 4 * (l1Poly3 res_slack_int : ℤ) * E_ttp_hi_den",
        f"    < 20 * S2 * {eps_in_E_den} := by decide +kernel",
        "",
        "end ThomsonN9.StageB.CapCertSosData",
        "",
    ]
    p_sos = LEAN_STAGEB / "CapCertSosData.lean"
    p_sos.write_text("\n".join(sos_lines))
    print(f"  Wrote {p_sos} ({p_sos.stat().st_size / 1024:.1f} KB)")

    # ---- Emit 19 Parallel 2D-Kronecker Slice Modules (T = -9..9) ----
    for T in range(-9, 10):
        tag = f"M{-T}" if T < 0 else str(T)
        ttag = f"m{-T}" if T < 0 else str(T)
        tlit = f"({T} : ℤ)" if T < 0 else str(T)
        slice_src = "\n".join([
            "import ThomsonN9.StageB.CapCertSosData",
            "",
            "set_option maxHeartbeats 16000000",
            "set_option maxRecDepth 200000",
            "",
            f"namespace ThomsonN9.StageB.CapCertSosSlice{tag}",
            "",
            "open ThomsonN9.StageB.CapCertSosData",
            "",
            f"theorem kron_t_{ttag} : checkKronCapAtT (wForT {tlit}) {tlit} = true := by decide +kernel",
            "",
            f"end ThomsonN9.StageB.CapCertSosSlice{tag}",
            "",
        ])
        (LEAN_STAGEB / f"CapCertSosSlice{tag}.lean").write_text(slice_src)
    print("  Wrote 19 parallel CapCertSosSlice{M9..9}.lean modules")

    # ---- Emit File 3: CapCertBernData.lean ----
    bern_lines = [
        "import ThomsonN9.StageB.CapCertHarmData",
        "import ThomsonN9.TableB1Data",
        "",
        "/-!",
        "# Thomson N = 9 Stage B — Cap Certificate L3 7-Piece Bernstein Tube Forcing Data",
        "",
        "Certifies `Peps(y) = K_bern * S2 * ((1 - eps_y) - 2y * H(1 - 2y^2)) ≥ 0` on the",
        "7 complement intervals of `[0, 9747/10000] \\ ⋃_{a=0..5} [y_a_lo, y_a_hi]`.",
        "-/",
        "",
        "set_option maxHeartbeats 16000000",
        "set_option maxRecDepth 200000",
        "",
        "namespace ThomsonN9.StageB.CapCertBernData",
        "",
        "open ThomsonN9.StageB.PolyKron",
        "open ThomsonN9.StageB.CapCertHarmData",
        "open ThomsonN9.TableB1Data",
        "",
        f"def const_peps : ℤ := {const_peps}",
        f"def Peps : List ℤ := {fmt_list_int(Peps)}",
        "",
        "theorem Peps_def_ok :",
        "    (padd Peps (pneg (padd [const_peps] (pscale (-K_bern) (twoYH H_int))))).all (· == 0) = true := by",
        "  decide +kernel",
        "",
        "theorem const_peps_ok : const_peps * eps_y_den = K_bern * S2 * (eps_y_den - eps_y_num) := by",
        "  decide +kernel",
        "",
    ]
    for a, (ylo, yhi) in enumerate(y_tubes):
        bern_lines.append(f"def yTubeLo_{a} : ℚ := {ylo.numerator} / {ylo.denominator}")
        bern_lines.append(f"def yTubeHi_{a} : ℚ := {yhi.numerator} / {yhi.denominator}")
    bern_lines.append("")
    for idx, bp in enumerate(bpieces):
        beta_str = "[" + ", ".join(str(x) for x in bp["beta"]) + "]"
        bern_lines += [
            f"def bp{idx} : BPiece := {{",
            f"  u1 := {bp['u1']}, u2 := {bp['u2']},",
            f"  w1 := {bp['w1']}, w2 := {bp['w2']},",
            f"  Lam := {bp['Lam']},",
            f"  β := {beta_str}",
            "}",
            f"theorem bp{idx}_ok : bp{idx}.check Peps = true := by decide +kernel",
            "",
        ]
    # Exact rational tube container checks against TableB1Data.nu1Lo..nu6Hi
    nu_names = [("nu1Lo", "nu1Hi"), ("nu2Lo", "nu2Hi"), ("nu3Lo", "nu3Hi"),
                ("nu4Lo", "nu4Hi"), ("nu5Lo", "nu5Hi"), ("nu6Lo", "nu6Hi")]
    for a, (nlo, nhi) in enumerate(nu_names):
        bern_lines += [
            f"theorem tube{a}_lo_ok : (1 : ℚ) - 2 * yTubeLo_{a} ^ 2 ≤ {nlo} + 1 / 10000 := by",
            f"  norm_num [yTubeLo_{a}, {nlo}]",
            f"theorem tube{a}_hi_ok : {nhi} - 1 / 10000 ≤ (1 : ℚ) - 2 * yTubeHi_{a} ^ 2 := by",
            f"  norm_num [yTubeHi_{a}, {nhi}]",
        ]
    bern_lines += [
        "",
        "end ThomsonN9.StageB.CapCertBernData",
        "",
    ]
    p_bern = LEAN_STAGEB / "CapCertBernData.lean"
    p_bern.write_text("\n".join(bern_lines))
    print(f"  Wrote {p_bern} ({p_bern.stat().st_size / 1024:.1f} KB) in {time.time() - t0:.2f}s")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", choices=["slab", "cap", "all"], default="all")
    ap.add_argument("--B-slab", type=int, default=36)
    ap.add_argument("--B-cap", type=int, default=76)
    args = ap.parse_args()
    if args.only in ("slab", "all"):
        export_slab(B=args.B_slab, D_kron=12)
    if args.only in ("cap", "all"):
        export_cap(B=args.B_cap, D_kron=20)
    print("\nALL EXPORTS & PRE-VERIFICATIONS SUCCEEDED!")


if __name__ == "__main__":
    main()
