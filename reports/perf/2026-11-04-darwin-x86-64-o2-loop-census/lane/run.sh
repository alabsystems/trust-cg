#!/bin/zsh
# OD-232 lane (wt-lk, lane/x86-o2-loop-knobs): gates, the knob bridge, then S26-0's pre-build
# O2 census (s26-design §7): a plain control and k1-k5, each compared with the control.
# Run as: BUILD_SLOT_MEM_GB=6 build-slot -- zsh run.sh   (the censuses wait for quiet + memory)
W=$HOME/tcg-scratch/wt-lk
cd $W || exit 9
L=$HOME/tcg-scratch/lk-run/logs
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
CMP=$HOME/trust-cg/reports/perf/2026-10-05-darwin-x86-64-census-slice12/census/census_compare.py
unset CARGO_TARGET_DIR
export TRUST_TARGO=$OV/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-lk-own
fail() { echo "GATE RED: $1"; exit 1; }
echo "== opt $(git rev-parse --short HEAD) $(date +%H:%M)"
for t in x86_loop_pass_opt_out_installers x86_pass_opt_out_installers; do
  bash scripts/trust_cargo.sh test -p trust-cg-opt --test $t -j${CARGO_BUILD_JOBS:-2} > $L/opt-$t.log 2>&1
  grep -E "^test |^test result" $L/opt-$t.log; grep -q "^test result: ok. 1 passed" $L/opt-$t.log || fail "$t"
done
bash scripts/trust_cargo.sh test -p trust-cg-opt --lib -j${CARGO_BUILD_JOBS:-2} -- x86_licm:: x86_loop_unroll:: x86_const_guard_elim:: > $L/opt-lib.log 2>&1
grep -E "^test result" $L/opt-lib.log; grep -q "^test result: ok" $L/opt-lib.log && ! grep -q FAILED $L/opt-lib.log || fail "opt lib tests"
echo "== codegen check $(date +%H:%M)"
bash scripts/trust_cargo.sh check -p trust-cg-codegen --lib --test x86_source_bound_body --test must_refuse_corpus -j${CARGO_BUILD_JOBS:-2} > $L/codegen-check.log 2>&1 || { grep -E "^error" $L/codegen-check.log | head; fail "codegen check"; }
echo "== fmt/docs $(date +%H:%M)"
TRUST_TARGO="$HOME/Library/Application Support/aterm/pkg/store/trust/6808/bin/targo" bash scripts/check_fmt.sh 2>&1 | tail -1 | grep -q "check_fmt: OK" || fail "fmt"
python3 scripts/check_documentation.py --check 2>&1 | tail -1 | grep -q "Maintained file links" || fail "docs"
echo "== bridge $(date +%H:%M)"
unset CARGO_TARGET_DIR TRUST_TARGO
STAMP=$(mktemp); sleep 1
BOUT=$(~/tcg-scratch/build_bridge.t011.sh "$W"); echo "$BOUT"
echo "$BOUT" | grep -qx "EXIT=0" || fail "bridge build"
D="$W/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
[ -f "$D" ] && [ "$D" -nt "$STAMP" ] || fail "no fresh bridge dylib"
cp "$D" ~/tcg-scratch/runs/lk.dylib && shasum -a 256 ~/tcg-scratch/runs/lk.dylib
C=~/tcg-scratch/census_t011_dylib.sh
R=~/tcg-scratch/runs
run_census() { # <tag> [knob ...]
  local tag=$1; shift
  echo "== census $tag [$*] $(date +%H:%M)"
  $C ~/tcg-scratch/runs/lk.dylib $tag 2 "$@" > $L/census-$tag.log 2>&1; tail -6 $L/census-$tag.log
}
run_census o2lk-plain
python3 $CMP $R/census-o2-s24a-f $R/census-o2lk-plain $R/cmp-o2lk-plain-vs-s24a > /dev/null 2>&1; head -6 $R/cmp-o2lk-plain-vs-s24a/compare.txt
run_census o2lk-k1 no-x86-loop-rotate
run_census o2lk-k2 no-x86-licm
run_census o2lk-k3 no-x86-licm no-x86-loop-rotate
run_census o2lk-k4 no-x86-licm no-x86-loop-rotate no-x86-strength-reduce no-x86-loop-unroll
run_census o2lk-k5 no-licm-pointer-loads no-x86-strength-reduce
for k in k1 k2 k3 k4 k5; do
  python3 $CMP $R/census-o2lk-plain $R/census-o2lk-$k $R/cmp-o2lk-$k > /dev/null 2>&1
  echo "== $k vs plain"; head -6 $R/cmp-o2lk-$k/compare.txt
done
echo "LK-DONE $(date +%H:%M)"
