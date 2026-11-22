#!/usr/bin/env python3
"""usage: compare_statements.py Challenge.tsv Solution.tsv
Every constant declared in Challenge.lean must exist in Solution.lean with the same kind,
universe-parameter count and fully pretty-printed (pp.all, pp.universes) type, and every
definition must also have the same pretty-printed value. This is an exact string comparison, not
a hash. Two kinds of exception exist:

* presence exemptions (SKIP): the three theorems not attempted yet (`thomson_nine_M1`,
  `thomson_nine`, `thomson_nine_unique`) need not be redeclared by the current solution. This
  is presence only: if the solution (or any dump compared against the challenge) DOES redeclare
  them, the type/value comparison below still applies in full — tampering with any statement
  anywhere is always detected (that is what scripts/negative-control.sh exercises).
* the values of theorems that Challenge leaves unproved (theorems have no value rows anyway).

Any axiom/opaque/quot declared in Solution.lean is an error. Exit 1 on any difference.
Adapted from references/thomson-n7-lean/formal/lean/scripts/compare_statements.py (which skipped
its unattempted stretch target `thomson_nine`; here the SKIP set is presence-only and shrinks to
empty as milestones are proved)."""
import sys, hashlib
def load(p):
    d = {}
    for l in open(p):
        l = l.rstrip("\n")
        if l:
            n, k, lv, ty, va = l.split("\t")
            d[n] = (k, lv, ty, va)
    return d
C, S = load(sys.argv[1]), load(sys.argv[2])
SKIP = set()
missing = [n for n in C if n not in S and n not in SKIP]
bad_type = [n for n in C if n in S and C[n][:3] != S[n][:3]]
bad_val = [n for n in C if n in S and C[n][0] == "def" and C[n][3] != S[n][3]]
new_ax = [n for n, v in S.items() if v[0] in ("axiom", "opaque", "quot")]
cmp_ = [n for n in C if n in S]
digest = hashlib.sha256("\n".join(f"{n}\t" + "\t".join(C[n]) for n in sorted(cmp_)).encode()).hexdigest()
print(f"Challenge constants: {len(C)}   Solution rows: {len(S)}")
print(f"compared: {len(cmp_)} ({sum(1 for n in cmp_ if C[n][0]=='def')} definitions with values)   skipped (not attempted): {sorted(n for n in C if n in SKIP)}")
print(f"sha256 of the compared Challenge text: {digest}")
print("missing in Solution:", missing)
print("kind/universe/type mismatches:", bad_type)
print("definition value mismatches:", bad_val)
print("axiom/opaque/quot declared in Solution:", new_ax)
ok = not (missing or bad_type or bad_val or new_ax)
print("STATEMENT COMPARISON:", "OK" if ok else "FAILED")
sys.exit(0 if ok else 1)
