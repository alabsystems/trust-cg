#!/bin/zsh
# Run the slice-22 controls once per rule mutant. First apply the mutants (`mutate.py <worktree>
# <stages>`; one test build serves all of them), build the library tests and copy the test binary
# aside; restore the files afterwards (never commit them). TCG_S22_MUTANT reaches the test binary
# directly (no cargo in between).
# usage: run_mutants.sh <worktree> <test binary> <out.txt> [mutant...]   (default: every mutant)
# FILTERS (space-separated libtest filters) narrows or widens the run; default: the slice-22
# library tests.
W=${1:?worktree}; BIN=${2:?test binary}; OUT=${3:?out}
shift 3
ALL=(div-no-call-event div-args-unobserved div-symbol-unchecked guard128-low-half-only
  guard128-wide-constant-stops liveness-division-no-call i128-division-stops
  limb-one-cross limb-widening addhi0-any-low acmul-unscoped acmul-creation-order guard-fold-off
  catnf-halves-swapped catnf-or-any-tail catnf-merge-any)
MUTANTS=("$@")
[ ${#MUTANTS} -eq 0 ] && MUTANTS=($ALL)
FILTERS=(${=FILTERS:-x86_source_bound_body::tests::slice22::})
: > "$OUT"
cd $W/crates/trust-cg-verify || exit 9
for m in none $MUTANTS; do
  while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
  LOG="$OUT.$m.log"
  START=$(date +%s)
  TCG_S22_MUTANT=$m RUST_MIN_STACK=67108864 nice -n 19 "$BIN" $FILTERS --skip host_qualification \
    --skip verifier_credits --test-threads=2 > "$LOG" 2>&1
  echo "== mutant $m ($(( $(date +%s) - START )) s)" >> "$OUT"
  grep -E "^test .*FAILED$|^test result" "$LOG" | sed 's/x86_source_bound_body::tests:://' | sort -u >> "$OUT"
done
cat "$OUT"
