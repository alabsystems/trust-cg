#!/bin/zsh
# Run the slice-21 controls once per rule mutant. First apply the mutants (`mutate.py
# <worktree>`; one test build serves all of them), build the library tests and copy the test
# binary aside; restore the files afterwards (never commit them). TCG_S21_MUTANT reaches the
# test binary directly (no cargo in between).
# usage: run_mutants.sh <test binary> <out.txt> [mutant...]   (default: every mutant)
# FILTERS (space-separated libtest filters) narrows or widens the run; default: the slice-21
# library tests and the OD-200 classification control.
BIN=${1:?test binary}; OUT=${2:?out}
shift 2
ALL=(key-no-format key-no-rounding key-no-operation no-operand-claims uint-no-top-bit
  stamp-ignored ucomis-pf-zero fcmp-olt-as-ult cvtt-saturating saturation-dropped
  fp-abstract-never cmpxchg16b-halves-swapped rbx-refused cas-result-from-r10
  pseudo-pairs-plain pseudo-any-access)
MUTANTS=("$@")
[ ${#MUTANTS} -eq 0 ] && MUTANTS=($ALL)
FILTERS=(${=FILTERS:-x86_source_bound_body::tests::slice21:: an_fp_abstract_refutation_is_uncredited_and_never_reported_refuted})
: > "$OUT"
cd $HOME/tcg-scratch/wt-s21/crates/trust-cg-verify || exit 9
for m in none $MUTANTS; do
  while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
  LOG="$OUT.$m.log"
  START=$(date +%s)
  TCG_S21_MUTANT=$m RUST_MIN_STACK=67108864 nice -n 19 "$BIN" $FILTERS --skip host_qualification \
    --skip verifier_credits --test-threads=2 > "$LOG" 2>&1
  echo "== mutant $m ($(( $(date +%s) - START )) s)" >> "$OUT"
  grep -E "^test .*FAILED$|^test result" "$LOG" | sed 's/x86_source_bound_body::tests:://' | sort -u >> "$OUT"
done
cat "$OUT"
