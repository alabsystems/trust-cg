#!/bin/zsh
# Run the review's controls once per mutant of `mutate_review.py` (apply it, build the library
# tests once, copy the test binary aside, restore the files; never commit the mutants).
# TCG_S22R_MUTANT reaches the test binary directly (no cargo in between).
# usage: run_review_mutants.sh <worktree> <test binary> <out.txt> [mutant...]   (default: every one)
W=${1:?worktree}; BIN=${2:?test binary}; OUT=${3:?out}
shift 3
ALL=(od210-routine-trusted od210-circular-trusted catnf-merge-two-terms catnf-extract-sext
  catnf-or-sext guard128-zero-never-fires)
MUTANTS=("$@")
[ ${#MUTANTS} -eq 0 ] && MUTANTS=($ALL)
FILTERS=(${=FILTERS:-x86_source_bound_body::tests::slice22::})
: > "$OUT"
cd $W/crates/trust-cg-verify || exit 9
for m in none $MUTANTS; do
  while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
  LOG="$OUT.$m.log"
  START=$(date +%s)
  TCG_S22R_MUTANT=$m RUST_MIN_STACK=67108864 nice -n 19 "$BIN" $FILTERS --skip host_qualification \
    --skip verifier_ --test-threads=2 > "$LOG" 2>&1
  echo "== mutant $m ($(( $(date +%s) - START )) s)" >> "$OUT"
  grep -E "^test .*FAILED$|^test result" "$LOG" | sed 's/x86_source_bound_body::tests:://' | sort -u >> "$OUT"
done
cat "$OUT"
