#!/bin/zsh
# The branch tree at stage 3 (wt-s19): its library tests, then the solver-free body gate and
# the slice-19 controls on that binary. One heavy lane; no AY.
S=$HOME/tcg-scratch/s19; T=$HOME/tcg-scratch/stage1-targets/wt-s19
$S/build_tests.sh $HOME/tcg-scratch/wt-s19 $S/logs/test_build_final.log > $S/logs/test_build_final.out 2>&1
grep -q "rc=0" $S/logs/test_build_final.out || { echo "TEST BUILD FAILED final"; grep -E "^error" -A 8 $S/logs/test_build_final.log | head -60; exit 1; }
bin=$(grep -o "$T/debug/deps/trust_cg_verify-[0-9a-f]*" $S/logs/test_build_final.log | tail -1)
cp $bin $S/testbin_final; echo "testbin_final <- $bin"
cd $HOME/tcg-scratch/wt-s19/crates/trust-cg-verify
echo "== body gate $(date +%H:%M)"
RUST_MIN_STACK=67108864 nice -n 19 $S/testbin_final x86_source_bound_body::tests:: --skip host_qualification --skip verifier_credits --skip canonical_migration_pairs --test-threads=2 > $S/logs/gate_final.log 2>&1
grep -E "^test result|FAILED" $S/logs/gate_final.log | head -20
echo "CHAIN-FINAL-DONE $(date)"
