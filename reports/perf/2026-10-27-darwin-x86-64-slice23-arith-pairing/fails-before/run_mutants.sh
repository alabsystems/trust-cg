#!/bin/zsh
# Run the slice-23 controls once per rule mutant. First apply the mutants (`mutate23.py
# <worktree>`; one test build serves all of them), build the library tests and copy the test
# binary aside; restore the files afterwards (never commit them). TCG_S23_MUTANT reaches the test
# binary directly (no cargo in between).
# usage: run_mutants.sh <worktree> <test binary> <out.txt> [mutant...]   (default: every mutant)
# FILTERS (space-separated libtest filters) narrows or widens the run; default: the slice-23
# library tests and the negative-memo real-path controls.
# build-slot admits one job at a time; 6 GiB is the documented memory override (coordinator, 2026-10-27).
export BUILD_SLOT_MEM_GB=6
W=${1:?worktree}; BIN=${2:?test binary}; OUT=${3:?out}
shift 3
ALL=(pair-no-operand-claims key-no-width key-no-signedness pair-stamp-only shift-key-full-count
  comm-creation-order generalized-sat-refutes generalize-not-rederived leaf-creation-order
  generalize-first paired-refutation-stands pairing-never-absorbed shift-no-value-claim
  pair-psabi-walk-only unpaired-units-are-paired shift-key-any-width narrow-shift-row-generic
  pairing-not-rederived pairing-unbound record-walk-from-key)
MUTANTS=("$@")
[ ${#MUTANTS} -eq 0 ] && MUTANTS=($ALL)
FILTERS=(${=FILTERS:-x86_source_bound_body::tests::slice23:: x86_source_bound_body::tests::negative_memo::})
: > "$OUT"
cd $W/crates/trust-cg-verify || exit 9
for m in none $MUTANTS; do
  while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
  LOG="$OUT.$m.log"
  START=$(date +%s)
  build-slot -- env TCG_S23_MUTANT=$m RUST_MIN_STACK=67108864 nice -n 19 "$BIN" $FILTERS --skip host_qualification \
    --skip verifier_credits --test-threads=2 > "$LOG" 2>&1
  echo "== mutant $m ($(( $(date +%s) - START )) s)" >> "$OUT"
  grep -E "^test .*FAILED$|^test result" "$LOG" | sed 's/x86_source_bound_body::tests:://' | sort -u >> "$OUT"
done
cat "$OUT"
