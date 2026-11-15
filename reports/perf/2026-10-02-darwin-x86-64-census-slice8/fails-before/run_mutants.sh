#!/bin/zsh
# Run the slice-8 library gate filter once per rule mutant. First apply the
# mutants (`mutate.py crates/trust-cg-verify/src/x86_source_bound_body.rs`; one
# build serves all of them), and restore the file with `git checkout`
# afterwards. TCG_S8_MUTANT reaches the test binary through
# scripts/trust_cargo.sh's runner.
# usage: run_mutants.sh <out.txt>
HERE="$(cd "$(dirname "$0")" && pwd)"
OUT=${1:?out}
: > "$OUT"
for m in none no-entry-bytes no-result-bytes reversed-lanes wide-result-lanes short-return-lanes \
    no-lane-metadata no-slot-table alias-zero-extends tied-as-move aggregate-as-pointer \
    raw-bool-bytes no-result-taint; do
  TCG_S8_MUTANT=$m zsh "$HERE/qualify.sh" "$OUT.$m.log" x86_source_bound_body::tests::slice8:: > /dev/null
  echo "== mutant $m" >> "$OUT"
  grep -E "^test .*FAILED|^test result" "$OUT.$m.log" | sed 's/x86_source_bound_body::tests::slice8:://' | sort -u >> "$OUT"
done
cat "$OUT"
