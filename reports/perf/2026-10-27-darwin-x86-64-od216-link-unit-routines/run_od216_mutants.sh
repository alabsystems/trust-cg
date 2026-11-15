#!/bin/zsh
# Run the OD-216 to OD-218 controls once per mutant of `mutate_od216.py` (apply it, build the
# trust-cg-verify library tests, the trust-cg-codegen `x86_source_bound_body` test and the
# trust-cg-opt library tests once, copy the binaries aside, restore the files; never commit the
# mutants). TCG_OD216_MUTANT reaches the test binaries directly (no cargo in between), and a
# codegen test's child process inherits it.
# usage: run_od216_mutants.sh <worktree> <verify lib test binary> <codegen body test binary>
#        <opt lib test binary> <out.txt> [mutant...]   (default: every one)
W=${1:?worktree}; VERIFY=${2:?verify binary}; CGBODY=${3:?codegen binary}; OPT=${4:?opt binary}
OUT=${5:?out}
shift 5
ALL=(od216-link-unit-unread od217-memory-routine-untrusted od218-memset-route-recursive)
MUTANTS=("$@")
[ ${#MUTANTS} -eq 0 ] && MUTANTS=($ALL)
VERIFY_FILTERS=(x86_source_bound_body::tests::slice13::a_memory_routine
  x86_source_bound_body::tests::slice13::the_slice_thirteen_fixture_modules
  x86_source_bound_body::tests::slice13::the_vectorizers_memset_call
  x86_source_bound_body::tests::slice22::a_routine
  x86_source_bound_body::tests::slice22::the_routine_never
  function_request::tests::request_input_identity_covers_operands_nan_payloads_and_exact_lir)
: > "$OUT"
for m in none $MUTANTS; do
  while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
  START=$(date +%s)
  (cd $W/crates/trust-cg-verify && TCG_OD216_MUTANT=$m RUST_MIN_STACK=67108864 nice -n 19 \
    "$VERIFY" $VERIFY_FILTERS --test-threads=2 > "$OUT.$m.verify.log" 2>&1)
  (cd $W/crates/trust-cg-codegen && TCG_OD216_MUTANT=$m RUST_MIN_STACK=67108864 nice -n 19 \
    "$CGBODY" x86_body_trace_names_a_routine --test-threads=1 > "$OUT.$m.codegen.log" 2>&1)
  (cd $W/crates/trust-cg-opt && TCG_OD216_MUTANT=$m RUST_MIN_STACK=67108864 nice -n 19 \
    "$OPT" x86_vectorize::tests::memset_route --test-threads=2 > "$OUT.$m.opt.log" 2>&1)
  echo "== mutant $m ($(( $(date +%s) - START )) s)" >> "$OUT"
  grep -ahE "^test .*(FAILED|ok)$|^test result" "$OUT.$m.verify.log" "$OUT.$m.codegen.log" "$OUT.$m.opt.log" \
    | sed 's/x86_source_bound_body::tests:://' | sort -u >> "$OUT"
done
cat "$OUT"
