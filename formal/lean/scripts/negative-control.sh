#!/usr/bin/env bash
# Negative controls for the Thomson N=9 Lean verification suite (run after scripts/check.sh):
#   (a) Statement-comparison negative control: flips the inequality of thomson_nine in a scratch
#       copy of the challenge file and verifies compare_statements.py rejects Solution.tsv against
#       ChallengeT.tsv, naming ONLY ThomsonN9.thomson_nine.
#   (b) Kernel-reduction negative control: asserts a false certificate boolean via `decide +kernel`
#       and verifies the Lean 4 kernel rejects it.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
LOGS="$ROOT/logs"; mkdir -p "$LOGS"
[ -s "$LOGS/Solution.tsv" ] || { echo "MISSING $LOGS/Solution.tsv: run bash scripts/check.sh first"; exit 1; }
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT

# (a) Statement tamper check against Solution.tsv
sed 's/coulombEnergy (triCapPrism z) ≤ coulombEnergy x := by/coulombEnergy x ≤ coulombEnergy (triCapPrism z) := by/' ComparatorChallenges/ThomsonN9.lean > "$T/ChallengeT.lean"
diff ComparatorChallenges/ThomsonN9.lean "$T/ChallengeT.lean" >/dev/null && { echo "mutation did not apply"; exit 1; }
lake env lean --root="$T" -o "$T/ChallengeT.olean" "$T/ChallengeT.lean" >/dev/null 2>&1 || true
{ echo 'import ChallengeT'; sed -e "s/DUMPMOD/ChallengeT/g" -e "s#OUTFILE#$T/ChallengeT.tsv#" scripts/DumpBody.lean; } > "$T/DumpT.lean"
LP="$(lake env printenv LEAN_PATH)"
lake env env LEAN_PATH="$T:$LP" lean "$T/DumpT.lean"
OUT="$(python3 scripts/compare_statements.py "$T/ChallengeT.tsv" "$LOGS/Solution.tsv" || true)"
printf '%s\n' "$OUT" | tee "$LOGS/negative-control.log"
if printf '%s\n' "$OUT" | grep -q "mismatches: \['ThomsonN9.thomson_nine'\]" && printf '%s\n' "$OUT" | grep -q "STATEMENT COMPARISON: FAILED"; then
  echo "NEGATIVE CONTROL (a) OK: statement flip against Solution.tsv detected (and only that theorem)"
else
  echo "NEGATIVE CONTROL (a) FAILED: the comparison did not flag the tampered theorem"; exit 1
fi

# (b) Kernel certificate tamper check (decide +kernel must reject a false certificate assertion)
cat > "$T/TamperKernel.lean" <<'LEAN'
import ThomsonN9.StageB.RigidityL4Data
theorem bad_cert : ThomsonN9.StageB.RigidityL4Data.checkTriSound = false := by
  decide +kernel
LEAN
if KOUT="$(lake env lean "$T/TamperKernel.lean" 2>&1)"; then
  echo "NEGATIVE CONTROL (b) FAILED: Lean accepted a false decide +kernel certificate!"
  exit 1
fi
if printf '%s\n' "$KOUT" | grep -qiE "type mismatch|proved that the proposition"; then
  echo "NEGATIVE CONTROL (b) OK: Lean kernel rejected false certificate assertion"
else
  echo "NEGATIVE CONTROL (b) UNEXPECTED ERROR: $KOUT"; exit 1
fi
