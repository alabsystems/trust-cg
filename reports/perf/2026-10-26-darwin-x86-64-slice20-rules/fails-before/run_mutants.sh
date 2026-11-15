#!/bin/zsh
# Run the slice-20 controls once per rule mutant. First apply the mutants (`mutate.py
# <worktree>`; one test build serves all of them), build the library tests and copy the test
# binary aside; restore the files afterwards (never commit them). TCG_S20_MUTANT reaches the
# test binary directly (no cargo in between).
# usage: run_mutants.sh <test binary> <out.txt> [mutant...]   (default: every mutant)
# FILTERS (space-separated libtest filters) narrows or widens the run; default: the slice-20
# library tests and slice 16's every-point control (the slice-20 rules' controls).
BIN=${1:?test binary}; OUT=${2:?out}
shift 2
ALL=(search-any-shape search-any-predecessor search-first-route-only searched-switch-per-path
  join-dead-always join-dead-keeps-first join-dead-machine-keeps
  i128-high-unrelated i128-high-pairing-from-low i128-pair-order-swapped i128-start-halves-swapped
  i128-machine-high-unset i128-pair-last-two-written
  shl128-no-bound boolread-any-byte boolread-bool-store-only ufixed-in-loop ufixed-none
  slots-count-64 slots-total-unbounded candidates-256 candidates-unbounded)
MUTANTS=("$@")
[ ${#MUTANTS} -eq 0 ] && MUTANTS=($ALL)
FILTERS=(${=FILTERS:-x86_source_bound_body::tests::slice20:: x86_source_bound_body::tests::slice16::every_earlier_fixture_cut_at_every_clean_point_holds_part_by_part})
: > "$OUT"
cd $HOME/tcg-scratch/wt-s20/crates/trust-cg-verify || exit 9
for m in none $MUTANTS; do
  while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
  LOG="$OUT.$m.log"
  START=$(date +%s)
  TCG_S20_MUTANT=$m RUST_MIN_STACK=67108864 nice -n 19 "$BIN" $FILTERS --skip host_qualification \
    --skip verifier_credits --skip canonical_migration_pairs --test-threads=2 > "$LOG" 2>&1
  echo "== mutant $m ($(( $(date +%s) - START )) s)" >> "$OUT"
  grep -E "^test .*FAILED$|^test result" "$LOG" | sed 's/x86_source_bound_body::tests:://' | sort -u >> "$OUT"
done
cat "$OUT"
