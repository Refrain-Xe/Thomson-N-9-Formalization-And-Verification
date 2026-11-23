#!/usr/bin/env bash
# Build a clean, self-contained arXiv source tarball (paper/arxiv-submission.tar.gz)
# containing ONLY main.tex and vector PDF figures (no PNG previews, build artifacts,
# macOS xattrs/PAX headers, or local username metadata).
set -euo pipefail
PAPER_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$PAPER_DIR"

FILES=(
  main.tex
  figures/fig_ttp.pdf
  figures/fig_overview.pdf
  figures/fig_minorant.pdf
)

for f in "${FILES[@]}"; do
  [ -f "$f" ] || { echo "MISSING required arXiv file: $f"; exit 1; }
done

OUT="$PAPER_DIR/arxiv-submission.tar.gz"
python3 - "$OUT" "${FILES[@]}" <<'PY'
import sys, tarfile
out, files = sys.argv[1], sys.argv[2:]
with tarfile.open(out, "w:gz", format=tarfile.USTAR_FORMAT) as tf:
    for f in files:
        ti = tf.gettarinfo(f, arcname=f)
        ti.uid = 0
        ti.gid = 0
        ti.uname = ""
        ti.gname = ""
        ti.pax_headers.clear()
        with open(f, "rb") as fp:
            tf.addfile(ti, fp)
PY

echo "Created $OUT ($(du -h "$OUT" | cut -f1))"
tar -tzvf "$OUT"
