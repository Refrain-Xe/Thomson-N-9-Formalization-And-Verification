#!/usr/bin/env bash
# Pin (or re-pin) the sha256 of every git-tracked file of the Lake package into SHA256SUMS.txt.
# After this, step 1 of scripts/check.sh enforces the hashes and also rejects tracked-but-unpinned
# files. SHA256SUMS.txt itself is never listed (as in the N=7 repository).
# Run this only when a file is meant to change: the point of the pin is that the trusted statement
# file cannot drift silently. Never run `lake update`; the dependency pins live in
# lakefile.toml / lake-manifest.json and must stay as shipped.
# Usage: bash scripts/pin_hashes.sh   (run from anywhere, needs git and python3)
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TOP="$(git -C "$ROOT" rev-parse --show-toplevel)"
cd "$TOP"
OUT="$ROOT/SHA256SUMS.txt"
TMP="$(mktemp)"
while IFS= read -r -d '' f; do
  case "$f" in formal/lean/SHA256SUMS.txt) continue ;; esac
  h="$(python3 -c 'import hashlib,sys;print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$f")"
  printf '%s  %s\n' "$h" "${f#formal/lean/}"
done < <(git ls-files -z -- formal/lean | sort -z) > "$TMP"
mv "$TMP" "$OUT"
chmod 0644 "$OUT"
echo "pinned $(wc -l < "$OUT" | tr -d ' ') files into $OUT"
