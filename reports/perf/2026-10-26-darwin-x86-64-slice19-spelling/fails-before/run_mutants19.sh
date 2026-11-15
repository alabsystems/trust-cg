#!/bin/zsh
# Run the slice-19 spelling controls once per rule mutant. First apply the mutants
# (`mutate19.py <worktree> <stage>`; one test build serves all of them) and build the library
# tests; restore the files afterwards (never commit them). TCG_S19_MUTANT reaches the test
# binary directly (no cargo in between).
# usage: run_mutants19.sh <worktree> <test binary> <out.txt> <mutant>...
# FILTERS (space-separated libtest filters) narrows the run; default: the solver-free body gate
# (the tool-gated qualification lanes skipped: they run one per process, qual/qualify19.sh).
W=${1:?worktree}; BIN=${2:?test binary}; OUT=${3:?out}
shift 3
MUTANTS=("$@")
# CONTROLS (a file of exact test names, one per line) replaces FILTERS.
FILTERS=(${=FILTERS:-x86_source_bound_body::tests::})
EXACT=()
if [ -n "${CONTROLS:-}" ]; then FILTERS=($(cat $CONTROLS)); EXACT=(--exact); fi
: > "$OUT"
cd $W/crates/trust-cg-verify || exit 9
for m in none $MUTANTS; do
  LOG="$OUT.$m.log"
  START=$(date +%s)
  TCG_S19_MUTANT=$m RUST_MIN_STACK=67108864 nice -n 19 "$BIN" $FILTERS $EXACT --skip host_qualification \
    --skip verifier_credits --skip canonical_migration_pairs --test-threads=${THREADS:-2} > "$LOG" 2>&1
  echo "== mutant $m ($(( $(date +%s) - START )) s)" >> "$OUT"
  grep -E "^test .*FAILED$|^test result" "$LOG" | sed 's/x86_source_bound_body::tests:://' | sort -u >> "$OUT"
done
echo MUTANTS-DONE >> "$OUT"
