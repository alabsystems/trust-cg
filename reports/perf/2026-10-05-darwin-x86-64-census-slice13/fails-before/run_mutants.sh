#!/bin/zsh
# Run the slice-13 library gate filter once per rule mutant (and the slice-9
# filter for the join rule). First apply the mutants (`mutate.py
# crates/trust-cg-verify/src/x86_source_bound_body.rs`; one build serves all of
# them), and restore the file with `git checkout` afterwards. TCG_S13_MUTANT
# reaches the test binary through scripts/trust_cargo.sh's runner.
# usage: [MUTANTS="none m1 .."] run_mutants.sh <worktree> <out.txt>
W=${1:?worktree}
OUT=${2:?out}
cd "$W" || exit 9
export TRUST_TARGO=${TRUST_TARGO:-$HOME/trust/build/x86_64-apple-darwin/stage1/bin/targo}
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$HOME/tcg-scratch/stage1-targets/$(basename "$PWD")}
export CARGO_BUILD_JOBS=2
: > "$OUT"
ALL="none store-no-escape no-escape-closure escaped-store-no-escape address-no-offset
  one-slot-name partial-address-read escape-sets-unchecked stack-param-at-8 rbp-any-disp
  stack-arg-at-8 stack-args-unobserved unwritten-outgoing-ok rsp-unbalanced memset-is-memcpy
  atomic-pairs-plain seqcst-store-admitted join-first-escapes rsp-open-at-return
  bool-byte-refused"
# MUTANTS="a b" runs only those.
for m in ${=${MUTANTS:-$ALL}}; do
  FILTER=x86_source_bound_body::tests::slice13::
  [ "$m" = join-first-escapes ] && FILTER=x86_source_bound_body::tests::slice9::a_join_of_different_escapes
  TCG_S13_MUTANT=$m nice bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -- \
    "$FILTER" > "$OUT.$m.log" 2>&1
  echo "== mutant $m ($FILTER)" >> "$OUT"
  grep -E "^test .*FAILED|^test result" "$OUT.$m.log" | sed 's/x86_source_bound_body::tests:://' | sort -u >> "$OUT"
done
cat "$OUT"
