#!/usr/bin/env bash
# Run every test of the 11 layout-gated trust-cg-codegen targets, one libtest
# process per test (--exact --include-ignored --test-threads=1, 1800 s alarm),
# the isolation run_public_release_codegen_tests.sh uses for the capstones.
set -u
WT="$1"; OUT="$2"
mkdir -p "$OUT"
cd "$WT" || exit 2
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$WT/target}"
pass=0; fail=0
for t in e2e_binding_defeq e2e_ctx_whnf_defeq e2e_defeq_cache e2e_eta_struct_ext e2e_fvar_opening e2e_lazy_delta e2e_phase_completion e2e_universe_integration e2e_universe_realnames e2e_tc_stitching e2e_frontend_roundtrip; do
  names=$(targo --unverified test --locked --quiet -p trust-cg-codegen --all-features --test "$t" -- --list --format terse 2>"$OUT/$t.list.err" | sed -n 's/: test$//p')
  n=$(printf '%s\n' "$names" | grep -c .)
  echo "== $t: $n tests" | tee -a "$OUT/summary.txt"
  for name in $names; do
    if perl -e 'alarm 1800; exec @ARGV' -- targo --unverified test --locked --quiet -p trust-cg-codegen --all-features --test "$t" -- --exact "$name" --include-ignored --test-threads=1 >"$OUT/$t.$name.log" 2>&1; then
      pass=$((pass+1)); echo "PASS $t::$name" >> "$OUT/summary.txt"
    else
      fail=$((fail+1)); echo "FAIL $t::$name rc=$?" | tee -a "$OUT/summary.txt"
    fi
  done
done
echo "TOTAL pass=$pass fail=$fail" | tee -a "$OUT/summary.txt"
