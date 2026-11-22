#!/usr/bin/env bash
# One-command check of the Thomson N=9 package against plain Mathlib (Comparator and a second kernel
# are future work, to be added as in the N=7 repository).
# Enforces six gates in sequence (any failure exits non-zero):
#   1. verifies the pinned SHA-256 hashes in SHA256SUMS.txt and rejects tracked-but-unpinned files,
#   2. scans ThomsonN9/Solution.lean for forbidden tokens,
#   3. fetches the pinned Mathlib cache,
#   4. builds both libraries, enforcing 4 expected `sorry` warnings in ComparatorChallenges and 0 in Solution,
#   5. prints the axioms of all 4 challenge theorems + 2 admissibility lemmas and rejects forbidden axioms,
#   6. compares all 36 challenge declarations against ThomsonN9/Solution.lean under pp.all + pp.universes.
# Needs: elan (Lean toolchain manager), git, python3, network for the first run (Mathlib + its
# cache), about 14 GB RAM and 10 GB disk. Never run `lake update`.
# Usage: bash scripts/check.sh                (run from anywhere)
#        SKIP_BUILD=1 bash scripts/check.sh   (only the checks that need no build)
# Adapted from references/thomson-n7-lean/formal/lean/scripts/check.sh.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
LOGS="$ROOT/logs"; mkdir -p "$LOGS"
CHAL=ComparatorChallenges/ThomsonN9.lean
SOL=ThomsonN9/Solution.lean
SUMS=SHA256SUMS.txt
step() { printf '\n== %s\n' "$*"; }
sha() { python3 -c 'import hashlib,sys;print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$1"; }

step "1. file identity (enforced once SHA256SUMS.txt is pinned)"
if [ -f "$SUMS" ]; then
  while read -r h f; do
    [ -e "$f" ] || { echo "MISSING pinned file: $f"; exit 1; }
    [ "$(sha "$f")" = "$h" ] || { echo "HASH MISMATCH: $f"; exit 1; }
  done < "$SUMS"
  echo "all $(wc -l < "$SUMS" | tr -d ' ') pinned hashes ok"
  if command -v git >/dev/null 2>&1 && git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    UNPINNED="$(git ls-files . | grep -v -x -F "$SUMS" | grep -v -x -F -f <(sed 's/^[0-9a-f]*  //' "$SUMS") || true)"
    [ -z "$UNPINNED" ] || { echo "TRACKED BUT UNPINNED FILES (run scripts/pin_hashes.sh): $UNPINNED"; exit 1; }
  fi
else
  echo "$SUMS not present yet: skipping the hash check."
  echo "pin it with scripts/pin_hashes.sh once the statements are frozen."
fi

step "2. token scan of $SOL and all supporting modules (any soundness-affecting hit is fatal)"
SCAN="$(grep -nE 'sorry|native_decide|ofReduceBool|ofReduceNat|trustCompiler|^\s*(private |protected |noncomputable )*(axiom|opaque|unsafe|partial) |set_option|implemented_by|@\[extern|csimp|^\s*(macro|syntax|elab|notation|infix|prefix|postfix|open Lean|initialize|run_cmd)|#eval|#exit' $SOL || true)"
if [ -n "$SCAN" ]; then
  echo "FORBIDDEN TOKEN in $SOL:"
  printf '%s\n' "$SCAN"
  exit 1
fi
echo "no forbidden tokens in $SOL"
python3 - <<'PY'
import pathlib, re, sys

def strip_lean_comments(s: str) -> str:
    out, i, n, depth = [], 0, len(s), 0
    while i < n:
        if depth == 0 and s[i:i+2] == "--":
            while i < n and s[i] != "\n":
                i += 1
        elif s[i:i+2] == "/-":
            depth += 1
            i += 2
        elif depth > 0 and s[i:i+2] == "-/":
            depth -= 1
            i += 2
        else:
            out.append("\n" if (depth > 0 and s[i] == "\n") else (" " if depth > 0 else s[i]))
            i += 1
    return "".join(out)

bad_pat = re.compile(
    r"\b(sorry|native_decide|ofReduceBool|ofReduceNat|trustCompiler|skipKernelTC)\b"
    r"|^\s*(private\s+|protected\s+|noncomputable\s+)*(axiom|opaque|unsafe|partial)\s"
    r"|implemented_by|@\[extern|\bcsimp\b|@\[delab"
    r"|^\s*(macro|syntax|elab|notation|infix|prefix|postfix|local\s+instance|open\s+Lean|initialize|run_cmd)\b"
    r"|#eval|#exit",
    re.MULTILINE,
)
opt_pat = re.compile(r"set_option\s+([A-Za-z0-9_.]+)")
allowed_opts = ("maxHeartbeats", "maxRecDepth", "linter.")

for p in sorted(pathlib.Path("ThomsonN9").rglob("*.lean")):
    clean = strip_lean_comments(p.read_text())
    m = bad_pat.search(clean)
    if m:
        line = clean[:m.start()].count("\n") + 1
        print(f"FORBIDDEN TOKEN in {p}:{line}: {m.group(0)!r}")
        sys.exit(1)
    for om in opt_pat.finditer(clean):
        opt = om.group(1)
        if not any(opt == a or opt.startswith(a) for a in allowed_opts):
            line = clean[:om.start()].count("\n") + 1
            print(f"FORBIDDEN set_option in {p}:{line}: {opt}")
            sys.exit(1)

lake_txt = pathlib.Path("lakefile.toml").read_text()
if re.search(r"leanOptions|moreLeanArgs|weakLeanArgs", lake_txt):
    print("FORBIDDEN compiler options in lakefile.toml")
    sys.exit(1)
print("all ThomsonN9/*.lean modules and lakefile.toml passed full soundness token scan")
PY

if [ "${SKIP_BUILD:-0}" = "1" ]; then echo; echo "SKIP_BUILD=1: stopping before the build."; exit 0; fi

step "3. toolchain and Mathlib (pinned by lean-toolchain, lakefile.toml, lake-manifest.json)"
cat lean-toolchain
lake exe cache get || echo "cache get failed: continuing, Mathlib will compile from source (hours)"

step "4. lake build (the challenge has 4 expected 'declaration uses sorry' warnings; the solution must have none)"
/usr/bin/time -p lake build ThomsonN9 ComparatorChallenges 2>&1 | tee "$LOGS/build.log" | tail -25
[ -s "$LOGS/build.log" ] || { echo "EMPTY BUILD LOG"; exit 1; }
CHAL_SORRY="$(grep -c "$CHAL.*sorry" "$LOGS/build.log" || true)"
SOL_SORRY="$(grep -c "$SOL.*sorry" "$LOGS/build.log" || true)"
echo "sorry warnings in $CHAL: $CHAL_SORRY (expect 4)"
echo "sorry warnings in $SOL:  $SOL_SORRY (expect 0)"
[ "$CHAL_SORRY" = "4" ] || { echo "SORRY COUNT MISMATCH in $CHAL: got $CHAL_SORRY, expected 4"; exit 1; }
[ "$SOL_SORRY" = "0" ] || { echo "SORRY COUNT MISMATCH in $SOL: got $SOL_SORRY, expected 0"; exit 1; }

step "5. axioms of all challenge theorems, thomson_nine_main, and admissibility lemmas (strict whitelist)"
lake env lean scripts/CheckAxioms.lean | tee "$LOGS/axioms.log"
[ -s "$LOGS/axioms.log" ] || { echo "EMPTY AXIOM LOG"; exit 1; }
python3 - "$LOGS/axioms.log" <<'PY'
import re, sys
allowed = {"propext", "Classical.choice", "Quot.sound"}
lines = open(sys.argv[1]).read().splitlines()
ax_lines = [l for l in lines if "depends on axioms:" in l]
if len(ax_lines) < 7:
    print(f"EXPECTED >= 7 '#print axioms' lines, got {len(ax_lines)}")
    sys.exit(1)
for l in ax_lines:
    m = re.search(r"depends on axioms: \[(.*)\]$", l)
    if not m:
        print(f"UNRECOGNIZED AXIOM LINE (e.g. does not depend on any axioms or malformed): {l}")
        sys.exit(1)
    axs = {a.strip() for a in m.group(1).split(",") if a.strip()}
    bad = axs - allowed
    if bad:
        print(f"DISALLOWED AXIOMS {sorted(bad)} in: {l}")
        sys.exit(1)
print(f"strict axiom whitelist OK across {len(ax_lines)} declarations: subset of {sorted(allowed)}")
PY

step "6. statement fidelity: every challenge constant redeclared by the solution must match it exactly"
dump() {  # $1 = module, $2 = tag
  { printf 'import %s\n' "$1"; sed -e "s/DUMPMOD/$1/g" -e "s#OUTFILE#$LOGS/$2.tsv#" scripts/DumpBody.lean; } > "$LOGS/Dump$2.lean"
  lake env lean "$LOGS/Dump$2.lean"
}
dump ComparatorChallenges.ThomsonN9 Challenge
cut -f1 "$LOGS/Challenge.names.tmp" 2>/dev/null || true
cut -f1 "$LOGS/Challenge.tsv" > "$LOGS/Challenge.names"
DUMP_ONLY="$LOGS/Challenge.names" dump ThomsonN9.Solution Solution
[ -s "$LOGS/Solution.tsv" ] || { echo "EMPTY Solution.tsv (Solution.lean must directly declare the challenge constants)"; exit 1; }
if python3 scripts/compare_statements.py "$LOGS/Challenge.tsv" "$LOGS/Solution.tsv" | tee "$LOGS/statement.log"; then
  grep -q '^compared: 36 ' "$LOGS/statement.log" || { echo "UNEXPECTED COMPARED COUNT"; exit 1; }
  echo "statement comparison OK"
else
  echo "STATEMENT COMPARISON FAILED"; exit 1
fi

step "DONE: all checks above passed (a failing step stops the script)"
