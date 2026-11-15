#!/bin/zsh
# Run the slice-12 library gate filter (and the slice-6/9 controls slice 12
# changed) once per rule mutant. First apply the mutants (`mutate.py
# crates/trust-cg-verify/src/x86_source_bound_body.rs`; one build serves all
# of them), and restore the file afterwards (never commit it). TCG_S12_MUTANT
# reaches the test binary through scripts/trust_cargo.sh's runner.
# usage: run_mutants.sh <out.txt> [mutant...]   (default: every mutant)
HERE="$(cd "$(dirname "$0")" && pwd)"
OUT=${1:?out}
shift
ALL=(none no-back-edge-relation no-entry-relation no-header-bytes no-machine-byte-check
  no-written-roots no-param-taint no-header-escape-union join-escape-refusal
  parallel-edge-copies no-edge-copy-temps psabi-bool-32 full-width-relation
  pairing-copy-source no-entry-header-check no-irreducible-check one-round header-address no-clean-registers no-upper-bound)
MUTANTS=("$@")
[ ${#MUTANTS} -eq 0 ] && MUTANTS=($ALL)
: > "$OUT"
for m in $MUTANTS; do
  TCG_S12_MUTANT=$m zsh "$HERE/qualify.sh" "$OUT.$m.log" x86_source_bound_body::tests::slice12:: \
    x86_source_bound_body::tests::slice9::a_join_of_different \
    x86_source_bound_body::tests::slice9::loops_and_the_size > /dev/null
  echo "== mutant $m" >> "$OUT"
  grep -E "^test .*(slice12|slice9::a_join_of_different|loops_and_the_size|slice6::.*loop).*FAILED|^test result" "$OUT.$m.log" \
    | sed 's/x86_source_bound_body::tests:://' | sort -u >> "$OUT"
done
cat "$OUT"
