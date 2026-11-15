#!/bin/zsh
# The slice-25.0 diagnostic census analysis (light; no build-slot): after
# census_diag.sh, the function-by-function no-verdict-change check against the
# O2 baseline (trace_diff.py), then the histogram of the scan's named rows
# (s_histogram.py), with the O0 cross-reference of the same S roots read from
# the O0 census objects of main's quotient code (census-o0-s24a) by the
# slice-25 design's o0_sib_sites.py (copied here with census_lib.py).
S=${0:A:h}
BASE=$HOME/tcg-scratch/runs/census-o2-s24a-f
NEW=$HOME/tcg-scratch/runs/census-o2-s25d
DUMP=$HOME/tcg-scratch/runs/dump-o2-s25d
O0OBJ=$HOME/tcg-scratch/runs/census-o0-s24a/obj
OUT=$HOME/tcg-scratch/s25-run/census/diag
mkdir -p $OUT
python3 -I $S/trace_diff.py $BASE $NEW $OUT/trace_diff > $OUT/trace_diff.txt; echo "trace_diff rc=$?"
cat $OUT/trace_diff.txt
python3 -I $S/s_roots.py $NEW > $OUT/s_roots.jsonl
python3 -I $S/o0_sib_sites.py $O0OBJ $OUT/s_roots.jsonl $OUT/o0_sib_sites.json
python3 -I $S/s_histogram.py $NEW $DUMP $OUT/histogram.md $OUT/s_rows.tsv $OUT/o0_sib_sites.json > /dev/null
echo "s_histogram rc=$?"
# Provenance and the commands that reproduce this directory.
{
  echo
  echo '## Provenance'
  echo
  echo "- Bridge: built by census_diag.sh from \`~/tcg-scratch/wt-s25d\` at \`$(git -C ~/tcg-scratch/wt-s25d rev-parse HEAD)\` (S25.0); census dylib \`~/tcg-scratch/runs/o2-s25d.dylib\` sha256 \`$(shasum -a 256 ~/tcg-scratch/runs/o2-s25d.dylib | cut -d' ' -f1)\`."
  echo "- Baseline: \`$BASE\` (dylib \`~/tcg-scratch/runs/o2-s24a-f.dylib\` sha256 \`$(shasum -a 256 ~/tcg-scratch/runs/o2-s24a-f.dylib | cut -d' ' -f1)\`, built at b342de091)."
  echo "- No-verdict-change check: \`$OUT/trace_diff.txt\` (trace_diff.py), anomalies $(wc -l < $OUT/trace_diff/anomalies.txt | tr -d ' ')."
  echo "- O0 cross-reference objects: \`$O0OBJ\`."
  echo "- Reproduce: \`BUILD_SLOT_MEM_GB=6 build-slot -- zsh $S/census_diag.sh\`, then \`zsh $S/diag_analysis.sh\`; per-function rows in \`$OUT/s_rows.tsv\`."
} >> $OUT/histogram.md
