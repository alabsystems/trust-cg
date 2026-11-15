#!/bin/zsh
# Run the slice-16 library gate once per rule mutant (and the whole x86 body
# gate, goldens included, for split-small). First apply the mutants
# (`mutate.py <worktree>`; one test build serves all of them) and build the
# library tests; restore the files afterwards (never commit them).
# TCG_S16_MUTANT reaches the test binary directly (no cargo in between).
# The four slowest tests (the large shapes and the cut-everywhere sweeps) run
# only for `none` and for a mutant no faster control fails (SLOW=1 forces
# them for every mutant).
# usage: run_mutants.sh <test binary> <out.txt> [mutant...]   (default: every mutant)
BIN=${1:?test binary}; OUT=${2:?out}
shift 2
ALL=(none no-cut-relation relation-first-edge-only carry-first-edge no-byte-items
  machine-bytes-unchecked upper-zero-unchecked part-credit-any no-inventory-check
  parts-incomplete-export split-small split-flags)
MUTANTS=("$@")
[ ${#MUTANTS} -eq 0 ] && MUTANTS=($ALL)
SKIP=(--skip qualification --skip negative_memo --skip host_qualification
  --skip verifier_credits --skip canonical_migration)
SLOWS=(--skip sources_past_the_lir_bounds --skip the_production_planner
  --skip every_earlier_fixture_cut_at_every_block --skip every_earlier_fixture_cut_at_every_clean_point)
: > "$OUT"
cd $HOME/tcg-scratch/wt-s16 || exit 9
for m in $MUTANTS; do
  FILTER=x86_source_bound_body::tests::slice16::
  [ $m = split-small ] && FILTER=x86_source_bound_body
  LOG="$OUT.$m.log"
  if [ $m = none ] || [ $m = split-small ] || [ -n "$SLOW" ]; then
    TCG_S16_MUTANT=$m RUST_MIN_STACK=16777216 nice -n 19 "$BIN" $FILTER $SKIP --test-threads=2 > "$LOG" 2>&1
  else
    TCG_S16_MUTANT=$m RUST_MIN_STACK=16777216 nice -n 19 "$BIN" $FILTER $SKIP $SLOWS --test-threads=2 > "$LOG" 2>&1
    if ! grep -qE "^test .*FAILED$" "$LOG"; then
      echo "(no fast control failed: the slow tests too)" >> "$LOG"
      TCG_S16_MUTANT=$m RUST_MIN_STACK=16777216 nice -n 19 "$BIN" $FILTER $SKIP --test-threads=2 >> "$LOG" 2>&1
    fi
  fi
  echo "== mutant $m" >> "$OUT"
  grep -E "^test .*FAILED$|^test result" "$LOG" | sed 's/x86_source_bound_body::tests:://' | sort -u >> "$OUT"
done
cat "$OUT"
