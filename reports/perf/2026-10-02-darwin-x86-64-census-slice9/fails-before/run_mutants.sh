#!/bin/zsh
# Run the slice-9 library gate filter once per rule mutant. First apply the
# mutants (`mutate.py crates/trust-cg-verify/src/x86_source_bound_body.rs
# crates/trust-cg-verify/src/x86_source_bound_body_slice9_tests.rs`; one
# build serves all of them), and restore both files afterwards (never commit
# them). TCG_S9_MUTANT reaches the test binary through
# scripts/trust_cargo.sh's runner.
# usage: run_mutants.sh <out.txt> [mutant...]   (default: every mutant)
HERE="$(cd "$(dirname "$0")" && pwd)"
OUT=${1:?out}
shift
ALL=(none no-edge-literals unguarded-items constant-join-guard first-edge-phi
  machine-first-phi no-merged-bytes no-machine-merged-bytes merged-bool-any
  flags-cross-blocks no-escape-agreement no-mixed-roots no-switch-distinct
  no-redefinition-check no-size-bounds same-edge-test no-inline
  no-inline-fallback no-cone no-drop-identities alu-flags-cross fixed-stride)
MUTANTS=("$@")
[ ${#MUTANTS} -eq 0 ] && MUTANTS=($ALL)
: > "$OUT"
for m in $MUTANTS; do
  TCG_S9_MUTANT=$m zsh "$HERE/qualify.sh" "$OUT.$m.log" x86_source_bound_body::tests::slice9:: > /dev/null
  echo "== mutant $m" >> "$OUT"
  grep -E "^test .*FAILED|^test result" "$OUT.$m.log" | sed 's/x86_source_bound_body::tests::slice9:://' | sort -u >> "$OUT"
done
cat "$OUT"
