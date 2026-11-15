#!/bin/zsh
# Run the slice-17 library gate once per rule mutant. First apply the mutants
# (`mutate.py <worktree>`; one test build serves all of them) and build the
# library tests; restore the files afterwards (never commit them).
# TCG_S17_MUTANT reaches the test binary directly (no cargo in between).
# usage: run_mutants.sh <test binary> <out.txt> [mutant...]   (default: every mutant)
BIN=${1:?test binary}; OUT=${2:?out}
shift 2
ALL=(none no-source-ib no-machine-ib ib-no-congruence store-no-update store-first-candidate
  candidates-one-short arg-offset-unobserved arg-slot-unchecked indexed-taint-dropped
  indexed-bool-unchecked bound-finder-admits-all dead-byte-ignores-loads dead-byte-keeps-value
  agep-stride-one bound-ignores-stride)
MUTANTS=("$@")
[ ${#MUTANTS} -eq 0 ] && MUTANTS=($ALL)
: > "$OUT"
cd $HOME/tcg-scratch/wt-s17/crates/trust-cg-verify || exit 9
for m in $MUTANTS; do
  LOG="$OUT.$m.log"
  TCG_S17_MUTANT=$m RUST_MIN_STACK=16777216 nice -n 19 "$BIN" x86_source_bound_body::tests::slice17:: \
    --test-threads=2 > "$LOG" 2>&1
  echo "== mutant $m" >> "$OUT"
  grep -E "^test .*FAILED$|^test result" "$LOG" | sed 's/x86_source_bound_body::tests:://' | sort -u >> "$OUT"
done
cat "$OUT"
