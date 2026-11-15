#!/bin/zsh
# Run the slice-15 library gate filter once per rule mutant. First apply the
# mutants (`mutate.py crates/trust-cg-verify/src/x86_source_bound_body.rs
# crates/trust-cg-lower/src/x86_64_isel.rs`; one build serves all of them),
# and restore both files with `git checkout` afterwards. TCG_S15_MUTANT reaches the test binary through
# scripts/trust_cargo.sh's runner.
# usage: [MUTANTS="none m1 .."] [FILTERS="f1 f2"] run_mutants.sh <worktree> <out.txt>
# (FILTERS: libtest filters instead of the slice-15 gate row; the mixed-width
# rows' controls of the first slices are `x86_source_bound_body::tests::
# wrong_width_or_extension_is_refused` and `...::pointer_casts_with_semantics_are_not_admitted`.)
W=${1:?worktree}
OUT=${2:?out}
cd "$W" || exit 9
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay12713
export TRUST_TARGO=${TRUST_TARGO:-$OVERLAY/bin/targo}
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$HOME/tcg-scratch/stage1-targets/$(basename "$PWD")}
export CARGO_BUILD_JOBS=2
: > "$OUT"
ALL="none neg-as-abs f32-nan-constant const-pool-any-size const-pool-any-row pxor-as-and
  mixed-copy-zero-extends mixed-alu-full-width bool-arg-byte derived-load-unobserved
  derived-store-keeps derived-escape-unchecked i128-stack-unaligned i128-stack-swapped
  selector-bool-copy"
for m in ${=${MUTANTS:-$ALL}}; do
  FILTER=${FILTERS:-x86_source_bound_body::tests::slice15::}
  TCG_S15_MUTANT=$m nice bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -- \
    ${=FILTER} > "$OUT.$m.log" 2>&1
  echo "== mutant $m ($FILTER)" >> "$OUT"
  grep -E "^test .*FAILED|^test result" "$OUT.$m.log" | sed 's/x86_source_bound_body::tests:://' | sort -u >> "$OUT"
done
cat "$OUT"
