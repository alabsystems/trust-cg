#!/bin/zsh
# Run the slice-10 library gate filter once per rule mutant. First apply the
# mutants (`mutate.py crates/trust-cg-verify/src/x86_source_bound_body.rs`; one
# build serves all of them), and restore the file with `git checkout`
# afterwards. TCG_S10_MUTANT reaches the test binary through
# scripts/trust_cargo.sh's runner.
# usage: run_mutants.sh <out.txt>
HERE="$(cd "$(dirname "$0")" && pwd)"
OUT=${1:?out}
: > "$OUT"
for m in none add-flags-unmodelled add-carry-as-overflow sub-borrow-inverted imul-flags-defined \
    mul-high-as-low mul-no-overflow overflow-unsigned overflow-narrow-mul popcount-low-byte \
    tied-and-as-move callee-not-observed call-kind-unpaired narrow-checked shift-count-unmasked \
    source-shift-unmasked; do
  TCG_S10_MUTANT=$m zsh "$HERE/qualify.sh" "$OUT.$m.log" x86_source_bound_body::tests::slice10:: > /dev/null
  echo "== mutant $m" >> "$OUT"
  grep -E "^test .*FAILED|^test result" "$OUT.$m.log" | sed 's/x86_source_bound_body::tests::slice10:://' | sort -u >> "$OUT"
done
cat "$OUT"
