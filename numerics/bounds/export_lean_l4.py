#!/usr/bin/env python3
"""export_lean_l4.py — Emit ThomsonN9/StageB/RigidityL4Data.lean with exact interval tables,
triNat/k4Nat bitmasks, 28 leaf witnesses, and kernel-checked soundness & DFS exhaustiveness."""
from __future__ import annotations

import math
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
OUT = REPO / "formal" / "lean" / "ThomsonN9" / "StageB" / "RigidityL4Data.lean"

# Exact nu containers from TableB1Data.lean
NU = [
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

S = 100000
rho = Fraction(1, 10000)
IV = [(math.floor((lo - rho) * S), math.ceil((hi + rho) * S)) for lo, hi in NU]

def iadd(x, y): return (x[0] + y[0], x[1] + y[1])
def isub(x, y): return (x[0] - y[1], x[1] - y[0])
def imul(x, y):
    ps = (x[0]*y[0], x[0]*y[1], x[1]*y[0], x[1]*y[1])
    return (min(ps), max(ps))
def isq(x):
    if x[0] <= 0 <= x[1]:
        return (0, max(x[0]*x[0], x[1]*x[1]))
    p0, p1 = x[0]*x[0], x[1]*x[1]
    return (min(p0, p1), max(p0, p1))
def iscale(k, x): return (k*x[0], k*x[1]) if k >= 0 else (k*x[1], k*x[0])

S2, S3, S4 = S*S, S**3, S**4
def detG_iv(a, b, c):
    ua, ub, uc = IV[a], IV[b], IV[c]
    t1 = iscale(2, imul(imul(ua, ub), uc))
    t2 = iscale(S, iadd(iadd(isq(ua), isq(ub)), isq(uc)))
    return isub(iadd((S3, S3), t1), t2)

def det4_iv(a, b, c, d, e, f):
    xa, xb, xc, xd, xe, xf = IV[a], IV[b], IV[c], IV[d], IV[e], IV[f]
    s2 = iadd(iadd(isq(xa), isq(xb)), iadd(iadd(isq(xc), isq(xd)), iadd(isq(xe), isq(xf))))
    t3 = iadd(iadd(imul(imul(xa, xb), xc), imul(imul(xa, xd), xe)),
              iadd(imul(imul(xb, xd), xf), imul(imul(xc, xe), xf)))
    p2 = iadd(iadd(imul(isq(xa), isq(xf)), imul(isq(xb), isq(xe))), imul(isq(xc), isq(xd)))
    c4 = iadd(iadd(imul(imul(xa, xc), imul(xf, xd)), imul(imul(xa, xe), imul(xf, xb))),
              imul(imul(xb, xc), imul(xe, xd)))
    res = isub((S4, S4), iscale(S2, s2))
    res = iadd(res, iscale(2*S, t3))
    res = iadd(res, p2)
    res = isub(res, iscale(2, c4))
    return res

def nodeOfN(i, j):
    if i == j: return 9
    if i // 3 == j // 3: return 2 if i // 3 == 2 else 4
    if i // 3 == 2: return 1 if (i % 3 + 3 - j % 3) % 3 == 1 else 5
    if j // 3 == 2: return 1 if (j % 3 + 3 - i % 3) % 3 == 1 else 5
    return 3 if i % 3 == j % 3 else 0

tri_ok = [[[detG_iv(a, b, c)[1] >= 0 for c in range(6)] for b in range(6)] for a in range(6)]
triNat = 0
triMask = [[0]*6 for _ in range(6)]
for a in range(6):
    for b in range(6):
        mask = sum((1 << c) for c in range(6) if tri_ok[a][b][c])
        triMask[a][b] = mask
        triNat |= (mask << ((a*6 + b)*6))

k4Nat = 0
k4Mask = {}
for a in range(6):
    for b in range(6):
        for c in range(6):
            if not tri_ok[a][b][c]: continue
            for d in range(6):
                for e in range(6):
                    if not tri_ok[a][d][e]: continue
                    m = 0
                    for f in range(6):
                        if tri_ok[b][d][f] and tri_ok[c][e][f]:
                            lo, hi = det4_iv(a, b, c, d, e, f)
                            if lo <= 0 <= hi:
                                m |= (1 << f)
                    k4Mask[(a, b, c, d, e)] = m
                    idx = ((((a*6 + b)*6 + c)*6 + d)*6 + e)*6
                    k4Nat |= (m << idx)

C = [[-1]*9 for _ in range(9)]
leaves = []
def dfs(v, u):
    if u == v:
        if v == 8:
            leaves.append([row[:] for row in C])
            return
        dfs(v + 1, 0)
        return
    init = ((63 >> C[0][v-1]) << C[0][v-1]) & 63 if (u == 0 and v >= 2) else 63
    m = init
    for a in range(u):
        m &= triMask[C[a][u]][C[a][v]]
        if m == 0: return
    if u >= 2:
        for a in range(u - 1):
            for b in range(a + 1, u):
                m &= k4Mask.get((C[a][b], C[a][u], C[b][u], C[a][v], C[b][v]), 0)
                if m == 0: return
    for col in range(6):
        if (m >> col) & 1:
            C[u][v] = C[v][u] = col
            dfs(v, u + 1)

dfs(1, 0)
assert len(leaves) == 28

def find_iso(leaf):
    perm = [-1]*9
    used = [False]*9
    def bt(i):
        if i == 9: return True
        for v in range(9):
            if used[v]: continue
            if all(leaf[perm[j]][v] == nodeOfN(j, i) for j in range(i)):
                perm[i] = v; used[v] = True
                if bt(i + 1): return True
                used[v] = False
        return False
    assert bt(0)
    return perm

def leaf_code(leaf):
    acc = 0
    for i in range(9):
        for j in range(i + 1, 9):
            acc = acc * 6 + leaf[i][j]
    return acc

witnesses = [(leaf_code(lf), find_iso(lf)) for lf in leaves]

# Pre-verify witness check
def lex_idx(i, j):
    assert 0 <= i < j < 9
    return i * (17 - i) // 2 + (j - i - 1)

for code, perm in witnesses:
    assert sorted(perm) == list(range(9))
    for i in range(9):
        for j in range(i + 1, 9):
            a, b = min(perm[i], perm[j]), max(perm[i], perm[j])
            k = lex_idx(a, b)
            dig = (code // (6 ** (35 - k))) % 6
            assert dig == nodeOfN(i, j)

lines = [
    "import ThomsonN9.TableB1",
    "",
    "/-!",
    "# Thomson N = 9 Stage B — L4 Combinatorial Rigidity Data & Kernel Certificates",
    "",
    "Auto-generated by `numerics/bounds/export_lean_l4.py`.",
    "Certifies by `decide +kernel`:",
    "1. `tri_sound_ok`: every excluded 3-tuple has `detG_iv.hi < 0`.",
    "2. `k4_sound_ok`: every valid-face excluded 4-tuple has `0 ∉ det4_iv`.",
    "3. `l4_k9_complete`: exhaustive sorted-row-0 `K_9` DFS lands in the 28-leaf table.",
    "4. `leaves_iso_ok`: every one of the 28 leaves carries a verified isomorphism to `TableB1.nodeOfN`.",
    "-/",
    "",
    "set_option maxHeartbeats 16000000",
    "set_option maxRecDepth 200000",
    "",
    "namespace ThomsonN9.StageB.RigidityL4Data",
    "",
    "open ThomsonN9.TableB1 ThomsonN9.TableB1Data",
    "",
    "structure IvZ where",
    "  lo : ℤ",
    "  hi : ℤ",
    "",
    "def ivAdd (x y : IvZ) : IvZ := ⟨x.lo + y.lo, x.hi + y.hi⟩",
    "def ivSub (x y : IvZ) : IvZ := ⟨x.lo - y.hi, x.hi - y.lo⟩",
    "def ivMul (x y : IvZ) : IvZ :=",
    "  let p1 := x.lo * y.lo; let p2 := x.lo * y.hi",
    "  let p3 := x.hi * y.lo; let p4 := x.hi * y.hi",
    "  ⟨min (min p1 p2) (min p3 p4), max (max p1 p2) (max p3 p4)⟩",
    "def ivSq (x : IvZ) : IvZ :=",
    "  let p1 := x.lo * x.lo; let p2 := x.hi * x.hi",
    "  if x.lo ≤ 0 ∧ 0 ≤ x.hi then ⟨0, max p1 p2⟩ else ⟨min p1 p2, max p1 p2⟩",
    "def ivScale (k : ℤ) (x : IvZ) : IvZ :=",
    "  if 0 ≤ k then ⟨k * x.lo, k * x.hi⟩ else ⟨k * x.hi, k * x.lo⟩",
    "",
    "def S_iv : ℤ := 100000",
    "def S2_iv : ℤ := 10000000000",
    "def S3_iv : ℤ := 1000000000000000",
    "def S4_iv : ℤ := 100000000000000000000",
    "",
    "def nodeIv : ℕ → IvZ",
    f"  | 0 => ⟨{IV[0][0]}, {IV[0][1]}⟩",
    f"  | 1 => ⟨{IV[1][0]}, {IV[1][1]}⟩",
    f"  | 2 => ⟨{IV[2][0]}, {IV[2][1]}⟩",
    f"  | 3 => ⟨{IV[3][0]}, {IV[3][1]}⟩",
    f"  | 4 => ⟨{IV[4][0]}, {IV[4][1]}⟩",
    f"  | _ => ⟨{IV[5][0]}, {IV[5][1]}⟩",
    "",
    "def detG_iv (a b c : ℕ) : IvZ :=",
    "  let ua := nodeIv a; let ub := nodeIv b; let uc := nodeIv c",
    "  let t1 := ivScale 2 (ivMul (ivMul ua ub) uc)",
    "  let t2 := ivScale S_iv (ivAdd (ivAdd (ivSq ua) (ivSq ub)) (ivSq uc))",
    "  ivSub (ivAdd ⟨S3_iv, S3_iv⟩ t1) t2",
    "",
    "def det4_iv (a b c d e f : ℕ) : IvZ :=",
    "  let xa := nodeIv a; let xb := nodeIv b; let xc := nodeIv c",
    "  let xd := nodeIv d; let xe := nodeIv e; let xf := nodeIv f",
    "  let s2 := ivAdd (ivAdd (ivSq xa) (ivSq xb)) (ivAdd (ivAdd (ivSq xc) (ivSq xd)) (ivAdd (ivSq xe) (ivSq xf)))",
    "  let t3 := ivAdd (ivAdd (ivMul (ivMul xa xb) xc) (ivMul (ivMul xa xd) xe))",
    "                  (ivAdd (ivMul (ivMul xb xd) xf) (ivMul (ivMul xc xe) xf))",
    "  let p2 := ivAdd (ivAdd (ivMul (ivSq xa) (ivSq xf)) (ivMul (ivSq xb) (ivSq xe))) (ivMul (ivSq xc) (ivSq xd))",
    "  let c4 := ivAdd (ivAdd (ivMul (ivMul xa xc) (ivMul xf xd)) (ivMul (ivMul xa xe) (ivMul xf xb)))",
    "                  (ivMul (ivMul xb xc) (ivMul xe xd))",
    "  ivSub (ivAdd (ivAdd (ivSub ⟨S4_iv, S4_iv⟩ (ivScale S2_iv s2)) (ivScale (2 * S_iv) t3)) p2) (ivScale 2 c4)",
    "",
    f"def triNat : ℕ := {hex(triNat)}",
    f"def k4Nat : ℕ := {hex(k4Nat)}",
    "",
    "def triMask (a b : ℕ) : ℕ := (triNat >>> ((a * 6 + b) * 6)) &&& 63",
    "def k4Mask (a b c d e : ℕ) : ℕ := (k4Nat >>> ((((((a * 6 + b) * 6 + c) * 6 + d) * 6 + e) * 6))) &&& 63",
    "",
    "def leafWitnesses : List (ℕ × List ℕ) := [",
]
for code, perm in witnesses:
    lines.append(f"  ({code}, {perm}),")
lines[-1] = lines[-1].rstrip(",")
lines += [
    "]",
    "",
    "def leavesList : List ℕ := leafWitnesses.map Prod.fst",
    "",
    "def eIdx (u v : ℕ) : ℕ := v * (v - 1) / 2 + u",
    "def getC (bits u v : ℕ) : ℕ := (bits >>> (eIdx u v * 3)) &&& 7",
    "def setC (bits u v col : ℕ) : ℕ := bits ||| (col <<< (eIdx u v * 3))",
    "",
    "def toLeafCode (bits : ℕ) : ℕ :=",
    "  let rec go : ℕ → ℕ → ℕ → ℕ → ℕ",
    "    | 0, _, _, acc => acc",
    "    | fuel + 1, i, j, acc =>",
    "      if i >= 9 then acc",
    "      else if j >= 9 then go fuel (i + 1) (i + 2) acc",
    "      else go fuel i (j + 1) (acc * 6 + getC bits i j)",
    "  go 50 0 1 0",
    "",
    "def filterTri (bits v u : ℕ) : ℕ → ℕ → ℕ",
    "  | 0, m => m",
    "  | a + 1, m =>",
    "    if m == 0 then 0",
    "    else filterTri bits v u a (m &&& triMask (getC bits a u) (getC bits a v))",
    "",
    "def filterK4Inner (bits v u a cau cav : ℕ) : ℕ → ℕ → ℕ",
    "  | 0, m => m",
    "  | k + 1, m =>",
    "    if m == 0 then 0",
    "    else",
    "      let b := a + 1 + k",
    "      let m2 := m &&& k4Mask (getC bits a b) cau (getC bits b u) cav (getC bits b v)",
    "      filterK4Inner bits v u a cau cav k m2",
    "",
    "def filterK4 (bits v u : ℕ) : ℕ → ℕ → ℕ",
    "  | 0, m => m",
    "  | a + 1, m =>",
    "    if m == 0 then 0",
    "    else",
    "      let cau := getC bits a u",
    "      let cav := getC bits a v",
    "      let m2 := filterK4Inner bits v u a cau cav (u - a - 1) m",
    "      filterK4 bits v u a m2",
    "",
    "def tryCols (f : ℕ → Bool) (mask : ℕ) : ℕ → Bool",
    "  | 0 => true",
    "  | c + 1 =>",
    "    let ok := if ((mask >>> c) &&& 1) == 1 then f c else true",
    "    ok && tryCols f mask c",
    "",
    "def checkAll : ℕ → ℕ → ℕ → ℕ → Bool",
    "  | 0, _, _, _ => false",
    "  | fuel + 1, v, u, bits =>",
    "    if u == v then",
    "      if v == 8 then leavesList.contains (toLeafCode bits)",
    "      else checkAll fuel (v + 1) 0 bits",
    "    else",
    "      let initMask :=",
    "        if u == 0 && v >= 2 then ((63 >>> (getC bits 0 (v - 1))) <<< (getC bits 0 (v - 1))) &&& 63",
    "        else 63",
    "      let m1 := filterTri bits v u u initMask",
    "      if m1 == 0 then true",
    "      else",
    "        let m2 := if u >= 2 then filterK4 bits v u (u - 1) m1 else m1",
    "        if m2 == 0 then true",
    "        else tryCols (fun col => checkAll fuel v (u + 1) (setC bits u v col)) m2 6",
    "",
    "def checkTriSound : Bool :=",
    "  (List.range 6).all fun a =>",
    "    (List.range 6).all fun b =>",
    "      (List.range 6).all fun c =>",
    "        if ((triMask a b >>> c) &&& 1) == 1 then true",
    "        else decide ((detG_iv a b c).hi < 0)",
    "",
    "def checkK4Sound : Bool :=",
    "  (List.range 6).all fun a =>",
    "    (List.range 6).all fun b =>",
    "      (List.range 6).all fun c =>",
    "        if ((triMask a b >>> c) &&& 1) == 0 then true",
    "        else (List.range 6).all fun d =>",
    "          (List.range 6).all fun e =>",
    "            if ((triMask a d >>> e) &&& 1) == 0 then true",
    "            else (List.range 6).all fun f =>",
    "              if ((triMask b d >>> f) &&& 1) == 0 || ((triMask c e >>> f) &&& 1) == 0 then true",
    "              else if ((k4Mask a b c d e >>> f) &&& 1) == 1 then true",
    "              else",
    "                let iv := det4_iv a b c d e f",
    "                decide (iv.hi < 0 ∨ 0 < iv.lo)",
    "",
    "def lexIdx (i j : ℕ) : ℕ := i * (17 - i) / 2 + (j - i - 1)",
    "",
    "def getLexEdge (code i j : ℕ) : ℕ :=",
    "  let a := min i j; let b := max i j",
    "  (code / (6 ^ (35 - lexIdx a b))) % 6",
    "",
    "def checkWitness (w : ℕ × List ℕ) : Bool :=",
    "  let code := w.1; let p := w.2",
    "  p.length == 9 &&",
    "  (List.range 9).all (fun k => p.contains k) &&",
    "  (List.range 9).all fun i =>",
    "    (List.range 9).all fun j =>",
    "      if i < j then getLexEdge code (p.getD i 0) (p.getD j 0) == nodeOfN i j",
    "      else true",
    "",
    "theorem tri_sound_ok : checkTriSound = true := by decide +kernel",
    "theorem k4_sound_ok : checkK4Sound = true := by decide +kernel",
    "theorem leaves_iso_ok : leafWitnesses.all checkWitness = true := by decide +kernel",
    "theorem l4_k9_complete : checkAll 46 1 0 0 = true := by decide +kernel",
    "",
    "-- Exact rational container containment proofs against TableB1Data.nu1Lo..nu6Hi",
    "theorem iv0_lo_ok : ((nodeIv 0).lo : ℚ) / 100000 ≤ nu1Lo - 1 / 10000 := by norm_num [nodeIv, nu1Lo]",
    "theorem iv0_hi_ok : nu1Hi + 1 / 10000 ≤ ((nodeIv 0).hi : ℚ) / 100000 := by norm_num [nodeIv, nu1Hi]",
    "theorem iv1_lo_ok : ((nodeIv 1).lo : ℚ) / 100000 ≤ nu2Lo - 1 / 10000 := by norm_num [nodeIv, nu2Lo]",
    "theorem iv1_hi_ok : nu2Hi + 1 / 10000 ≤ ((nodeIv 1).hi : ℚ) / 100000 := by norm_num [nodeIv, nu2Hi]",
    "theorem iv2_lo_ok : ((nodeIv 2).lo : ℚ) / 100000 ≤ nu3Lo - 1 / 10000 := by norm_num [nodeIv, nu3Lo]",
    "theorem iv2_hi_ok : nu3Hi + 1 / 10000 ≤ ((nodeIv 2).hi : ℚ) / 100000 := by norm_num [nodeIv, nu3Hi]",
    "theorem iv3_lo_ok : ((nodeIv 3).lo : ℚ) / 100000 ≤ nu4Lo - 1 / 10000 := by norm_num [nodeIv, nu4Lo]",
    "theorem iv3_hi_ok : nu4Hi + 1 / 10000 ≤ ((nodeIv 3).hi : ℚ) / 100000 := by norm_num [nodeIv, nu4Hi]",
    "theorem iv4_lo_ok : ((nodeIv 4).lo : ℚ) / 100000 ≤ nu5Lo - 1 / 10000 := by norm_num [nodeIv, nu5Lo]",
    "theorem iv4_hi_ok : nu5Hi + 1 / 10000 ≤ ((nodeIv 4).hi : ℚ) / 100000 := by norm_num [nodeIv, nu5Hi]",
    "theorem iv5_lo_ok : ((nodeIv 5).lo : ℚ) / 100000 ≤ nu6Lo - 1 / 10000 := by norm_num [nodeIv, nu6Lo]",
    "theorem iv5_hi_ok : nu6Hi + 1 / 10000 ≤ ((nodeIv 5).hi : ℚ) / 100000 := by norm_num [nodeIv, nu6Hi]",
    "",
    "end ThomsonN9.StageB.RigidityL4Data",
    "",
]

OUT.write_text("\n".join(lines))
print(f"Wrote {OUT} ({OUT.stat().st_size / 1024:.1f} KB)")
