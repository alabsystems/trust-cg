#!/bin/zsh
# After the codegen gate (chain_meas5.sh's "== regress" line): the library tests with the tables
# the final qualification measured (final4); after the regression replay, the three lanes whose
# records moved, one test per process.
S=$HOME/tcg-scratch/s19; T=$HOME/tcg-scratch/stage1-targets/wt-s19; W=$HOME/tcg-scratch/wt-s19
until grep -q "== regress" $S/logs/chain_meas5.log 2>/dev/null || ! pgrep -f "[c]hain_meas5.sh" >/dev/null; do sleep 30; done
until grep -q "GATE-FINAL3-DONE" $S/logs/gate_after_qual.log 2>/dev/null || ! pgrep -f "[g]ate_after_qual.sh" >/dev/null; do sleep 30; done
$S/build_tests.sh $W $S/logs/test_build_final4.log > $S/logs/test_build_final4.out 2>&1
grep -q "rc=0" $S/logs/test_build_final4.out || { echo "TEST BUILD FAILED final4"; grep -E "^error" -A 8 $S/logs/test_build_final4.log | head -40; exit 1; }
bin=$(grep -o "$T/debug/deps/trust_cg_verify-[0-9a-f]*" $S/logs/test_build_final4.log | tail -1); cp $bin $S/testbin_final4; echo "testbin_final4 <- $bin"
until grep -q "CHAIN-MEAS5-DONE" $S/logs/chain_meas5.log 2>/dev/null || ! pgrep -f "[c]hain_meas5.sh" >/dev/null; do sleep 30; done
rm -rf $S/qual/final-rerun
$S/qual/qualify19.sh $W $S/testbin_final4 $S/qual/final-rerun \
  x86_source_bound_body::tests::host_qualification_replays_the_canonical_body_theorems \
  x86_source_bound_body::tests::slice20_qualification::host_qualification_replays_the_slice_twenty_body_theorems \
  x86_source_bound_body::tests::slice20_qualification::verifier_credits_every_bound_slice_twenty_row_with_the_replayed_body_theorem
cat $S/qual/final-rerun/summary.txt
echo "CHAIN-REQUAL-DONE $(date)"
