#!/bin/zsh
# Slice-23 review fixes (pre-merge): build the library tests (w2), run the slice-23 and
# negative-memo controls, then build the whole-core probe and run it over runs/core-ir-s23,
# comparing it byte for byte with 9f7aa5b2b's run (s23-run/all/p4). Every step through build-slot.
F=$HOME/tcg-scratch/s23-fix; S=$HOME/tcg-scratch/s23-run; W=$HOME/tcg-scratch/wt-s23
export BUILD_SLOT_MEM_GB=6
step() { echo "$(date +%H:%M:%S) $*" >> $F/logs/chain_w2.txt; }
step START $(git -C $W rev-parse --short HEAD) dirty=$(git -C $W status --porcelain -- crates | wc -l | tr -d ' ')
$F/build_test.sh w2 > $F/logs/build_w2.out 2>&1 || { step "w2 BUILD FAILED"; exit 1; }
step "w2 built"
(cd $W/crates/trust-cg-verify && build-slot -- env RUST_MIN_STACK=67108864 nice -n 19 $F/testbin_w2 \
  x86_source_bound_body::tests::slice23:: x86_source_bound_body::tests::negative_memo:: \
  --skip host_qualification --skip verifier_credits --test-threads=2) > $F/logs/s23_w2.log 2>&1
step "controls exit=$? $(grep -E '^test result' $F/logs/s23_w2.log | tail -1)"
$F/probe/build_probe.sh w2 > $F/logs/probe_build_w2.out 2>&1
[ -x $F/probe/x86_body_probe_w2 ] || { step "probe build failed"; exit 2; }
step "probe built"
build-slot -- zsh $S/probe/run_probe_all.sh $F/probe/x86_body_probe_w2 $HOME/tcg-scratch/runs/core-ir-s23 $F/all/w2 > $F/logs/all_w2.out 2>&1
step "probe ran: $(tail -1 $F/logs/all_w2.out)"
diff -r $S/all/p4/smt2 $F/all/w2/smt2 > $F/logs/probe_diff_w2.txt 2>&1; D1=$?
diff $S/all/p4/cf.tsv $F/all/w2/cf.tsv > $F/logs/probe_cf_diff_w2.txt 2>&1; D2=$?
step "probe compare: smt2 diff exit=$D1 ($(wc -l < $F/logs/probe_diff_w2.txt) lines), cf.tsv diff exit=$D2, files=$(ls $F/all/w2/smt2 | wc -l | tr -d ' ')"
step CHAIN-W2-DONE
