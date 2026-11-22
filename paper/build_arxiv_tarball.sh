#!/usr/bin/env bash
# Build a clean, self-contained arXiv source tarball (paper/arxiv-submission.tar.gz)
# containing ONLY main.tex and vector PDF figures (no PNG previews or build artifacts).
set -euo pipefail
PAPER_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$PAPER_DIR"

for f in main.tex figures/fig_ttp.pdf figures/fig_overview.pdf figures/fig_minorant.pdf; do
  [ -f "$f" ] || { echo "MISSING required arXiv file: $f"; exit 1; }
done

OUT="$PAPER_DIR/arxiv-submission.tar.gz"
COPYFILE_DISABLE=1 tar -czf "$OUT" \
  main.tex \
  figures/fig_ttp.pdf \
  figures/fig_overview.pdf \
  figures/fig_minorant.pdf

echo "Created $OUT ($(du -h "$OUT" | cut -f1))"
tar -tzvf "$OUT"
