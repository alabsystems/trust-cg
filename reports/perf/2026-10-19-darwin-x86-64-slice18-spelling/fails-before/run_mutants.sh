#!/bin/zsh
# Run the x86 body library gate's spelling controls once per slice-18 rule mutant. First apply
# the mutants (`mutate.py <worktree> <stage>...`; one test build serves all of them) and build
# the library tests; restore the files afterwards (never commit them). TCG_S18_MUTANT reaches
# the test binary directly (no cargo in between).
# usage: run_mutants.sh <test binary> <out.txt> <mutant>...
# FILTERS (space-separated libtest filters) narrows the run; default: the whole solver-free body
# gate (the tool-gated qualification lanes skipped: they run one per process, census/qualify.sh).
BIN=${1:?test binary}; OUT=${2:?out}
shift 2
MUTANTS=("$@")
FILTERS=(${=FILTERS:-x86_source_bound_body::tests::})
: > "$OUT"
cd $HOME/tcg-scratch/wt-s18/crates/trust-cg-verify || exit 9
for m in none $MUTANTS; do
  LOG="$OUT.$m.log"
  START=$(date +%s)
  TCG_S18_MUTANT=$m RUST_MIN_STACK=67108864 nice -n 19 "$BIN" $FILTERS --skip host_qualification \
    --skip verifier_credits --skip canonical_migration_pairs --test-threads=3 > "$LOG" 2>&1
  echo "== mutant $m ($(( $(date +%s) - START )) s)" >> "$OUT"
  grep -E "^test .*FAILED$|^test result" "$LOG" | sed 's/x86_source_bound_body::tests:://' | sort -u >> "$OUT"
done
cat "$OUT"
