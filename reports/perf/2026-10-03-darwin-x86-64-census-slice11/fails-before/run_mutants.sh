#!/bin/zsh
# Run the slice-11 library gate filter (and the slice-1 controls the shift
# spelling and the CL count touch) once per rule mutant. First apply the
# mutants (`mutate.py crates/trust-cg-verify/src/x86_source_bound_body.rs`; one
# build serves all of them), and restore the file with `git checkout`
# afterwards. TCG_S11_MUTANT reaches the test binary through
# scripts/trust_cargo.sh's runner.
# usage: run_mutants.sh <out.txt>
HERE="$(cd "$(dirname "$0")" && pwd)"
OUT=${1:?out}
: > "$OUT"
for m in none param-halves-swapped result-halves-swapped arg-halves-swapped call-result-swapped \
    access-no-offset store-low-twice iconst-zero-extended iconst128-swapped adc-no-carry \
    sbb-adds-carry carry-from-anything cl-shift-reads-zero cl-constant-unmasked sse-one-class \
    sse-result-in-rax movss-keeps-upper xmm-survive-calls i128-variable-shift ashr-as-logical \
    wide-names i128-field-refused; do
  TCG_S11_MUTANT=$m zsh "$HERE/qualify.sh" "$OUT.$m.log" x86_source_bound_body::tests::slice11:: > /dev/null
  echo "== mutant $m" >> "$OUT"
  grep -E "^test .*FAILED|^test result" "$OUT.$m.log" | sed 's/x86_source_bound_body::tests::slice11:://' | sort -u >> "$OUT"
done
cat "$OUT"
