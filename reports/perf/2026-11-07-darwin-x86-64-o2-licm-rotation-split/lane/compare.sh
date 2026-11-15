#!/bin/zsh
# Read-only comparisons of the two single-knob censuses with census-o2-m301 (and lr), outputs here.
R=$HOME/tcg-scratch/runs; O=$HOME/tcg-scratch/s26-rebase
P=$HOME/trust-cg/reports/perf
C=$P/2026-10-06-darwin-x86-64-census-slice15/census/census_compare.py
RC=$P/2026-09-27-darwin-x86-64-census/root_classes.py
F=$P/2026-11-04-darwin-x86-64-slice25-sib-rows/scripts/census_s25.py
for T in o2k-m301-l o2k-m301-r; do
  mkdir -p $O/$T
  python3 -I $C $R/census-o2-m301 $R/census-$T $O/$T/vs-o2-m301 > $O/$T/vs-o2-m301.log 2>&1; echo "$T compare rc=$?"
  head -14 $O/$T/vs-o2-m301/compare.txt
  python3 -I $RC $R/census-$T > $O/$T/root_classes.txt 2>&1; echo "$T root_classes rc=$?"
  python3 -I $F $R/census-o2-m301 $R/census-$T $O/$T/followup > /dev/null 2>&1; echo "$T followup rc=$?"
  python3 -I $C $R/census-$T $R/census-o2k-m301-lr $O/$T/lr-vs-$T > $O/$T/lr-vs-$T.log 2>&1; echo "lr vs $T rc=$?"
  head -6 $O/$T/lr-vs-$T/compare.txt
done
