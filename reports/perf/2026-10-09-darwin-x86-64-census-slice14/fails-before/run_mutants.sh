#!/bin/zsh
# Run the slice-14 library gate filter once per rule mutant. First apply the
# mutants (`mutate.py crates/trust-cg-verify/src/x86_source_bound_body.rs` and
# `mutate_selector.py crates/trust-cg-lower/src/x86_64_isel.rs`; one
# build serves all of them), and restore the file afterwards (never commit
# it). TCG_S14_MUTANT reaches the test binary through scripts/trust_cargo.sh's
# runner.
# usage: run_mutants.sh <out.txt> [mutant...]   (default: every mutant)
HERE="$(cd "$(dirname "$0")" && pwd)"
OUT=${1:?out}
shift
ALL=(none no-undefined-stop no-constant-fold path-insensitive-stop no-join-stop no-guard-claim fault-traps
  no-liveness no-division-fault canonical-always cqo-zero div-swapped xor-reads
  refuse-shared-targets first-case-only first-route-only table-any-index table-index-shift
  dispatch-unrecognized pair-always pow2-division-shift pow2-product-shift selector-64-bit-copy)
MUTANTS=("$@")
[ ${#MUTANTS} -eq 0 ] && MUTANTS=($ALL)
: > "$OUT"
for m in $MUTANTS; do
  TCG_S14_MUTANT=$m zsh "$HERE/qualify.sh" "$OUT.$m.log" x86_source_bound_body::tests::slice14:: > /dev/null
  echo "== mutant $m" >> "$OUT"
  grep -E "^test .*slice14.*FAILED|^test result" "$OUT.$m.log" \
    | sed 's/x86_source_bound_body::tests:://' | sort -u >> "$OUT"
done
cat "$OUT"
