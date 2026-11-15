#!/bin/zsh
# Slice 24c's ceiling census on the slice-25 base (design
# ~/tcg-scratch/s24c-design/README.md §7 "Before building" and its addendum).
#
# The census itself, from slice 25's existing release bridge (head d92b944fe,
# dylib ~/tcg-scratch/runs/o2-s25.dylib, whose O2 objects equal the merged head
# a617488aa's), with if-conversion and the cmov swap off:
#   BUILD_SLOT_MEM_GB=6 build-slot -- ~/tcg-scratch/census_t011_dylib.sh \
#     ~/tcg-scratch/runs/o2-s25.dylib o2k-s25-nifc 2 no-x86-ifconvert no-x86-cmov-swap
# (log ~/tcg-scratch/s24c-run/logs/census-o2k-s25-nifc.log). This script is the
# read-only analysis after it: slice 15's census_compare.py against
# census-o2-s25, root_classes.py on both sides, and ceiling_s25.py (first
# refusal of every promoted root, the candidate shapes and how many bind).
#
# Local copies (byte-identical to their sources):
#   census_compare.py  reports/perf/2026-10-06-darwin-x86-64-census-slice15/census/ (sha256 73e1819e…)
#   root_classes.py    reports/perf/2026-09-27-darwin-x86-64-census/ at a617488aa (sha256 0a2f4d4f…)
# Run as: zsh ceiling.sh   (no build, no slot needed: it reads census dirs only)
S=${0:A:h}
R=$HOME/tcg-scratch/runs
BASE=$R/census-o2-s25
NEW=$R/census-o2k-s25-nifc
OUT=$HOME/tcg-scratch/s24c-run/census/nifc
OLD=$HOME/tcg-scratch/s24c-design/work/angleB/candidates.tsv
grep -q CENSUS-DONE $HOME/tcg-scratch/s24c-run/logs/census-o2k-s25-nifc.log || { echo "census not done"; exit 3; }
mkdir -p $OUT
python3 -I $S/census_compare.py $BASE $NEW $OUT || echo "compare rc=$?"
python3 -I $S/root_classes.py $BASE > $OUT/root_classes.base.txt || echo "base root classes rc=$?"
python3 -I $S/root_classes.py $NEW > $OUT/root_classes.txt || echo "nifc root classes rc=$?"
python3 -I $S/ceiling_s25.py $BASE $NEW $OUT/ceiling $OLD || echo "ceiling rc=$?"
echo "CEILING-DONE $(date +%H:%M)"
