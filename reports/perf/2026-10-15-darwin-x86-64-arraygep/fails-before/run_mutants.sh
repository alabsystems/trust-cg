#!/bin/zsh
# Run the OD-185 library gate (`x86_source_bound_body::tests::arraygep::`) once
# per rule mutant. First apply the mutants (`mutate.py <worktree>`; one test
# build serves all of them) and build the library tests; restore the file
# afterwards (never commit it). TCG_AGEP_MUTANT reaches the test binary
# directly (no cargo in between).
# usage: run_mutants.sh <test binary> <out.txt> [mutant...]   (default: every mutant)
BIN=${1:?test binary}; OUT=${2:?out}
shift 2
ALL=(none source-refused source-unscaled source-unindexed source-affine-off any-index-width
  frame-refused frame-unscaled frame-wrapping frame-variable-zero layout-unchecked
  machine-frame-off machine-frame-unscaled machine-imul-fold-off machine-affine-off
  stackaddr-hint-off gep-hint-aggregate)
MUTANTS=("$@")
[ ${#MUTANTS} -eq 0 ] && MUTANTS=($ALL)
SKIP=(--skip qualification --skip negative_memo --skip host_qualification
  --skip verifier_credits --skip canonical_migration)
: > "$OUT"
for m in $MUTANTS; do
  LOG="$OUT.$m.log"
  TCG_AGEP_MUTANT=$m RUST_MIN_STACK=16777216 nice -n 19 "$BIN" x86_source_bound_body::tests::arraygep:: $SKIP --test-threads=2 > "$LOG" 2>&1
  echo "== mutant $m" >> "$OUT"
  grep -E "^test .*FAILED$|^test result" "$LOG" | sed 's/x86_source_bound_body::tests:://' | sort -u >> "$OUT"
done
cat "$OUT"
