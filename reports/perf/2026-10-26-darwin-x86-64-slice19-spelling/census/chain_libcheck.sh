#!/bin/zsh
# Whether the 18 library-test failures of the final code fail on main fc03f94f2 too: main's
# library tests (the control tree) built after the lint run, then both binaries run exactly
# those tests after the regression replay and the lane re-run (they start real and fixture
# solvers). One heavy lane; one solver at a time.
S=$HOME/tcg-scratch/s19; T=$HOME/tcg-scratch/stage1-targets/wt-s19
until grep -q "TIPPY-DONE" $S/logs/tippy_after_gate.log 2>/dev/null || ! pgrep -f "[t]ippy_after_gate.sh" >/dev/null; do sleep 30; done
$S/build_tests.sh $HOME/tcg-scratch/wt-s19-base $S/logs/test_build_main20.log > $S/logs/test_build_main20.out 2>&1
bin=$(grep -o "$T/debug/deps/trust_cg_verify-[0-9a-f]*" $S/logs/test_build_main20.log | tail -1); cp $bin $S/testbin_main20; echo "testbin_main20 <- $bin"
until grep -q "CHAIN-REQUAL-DONE" $S/logs/chain_requal.log 2>/dev/null || ! pgrep -f "[c]hain_requal.sh" >/dev/null; do sleep 30; done
for tag_tree in main20:wt-s19-base final4:wt-s19; do
  tag=${tag_tree%%:*}; tree=${tag_tree#*:}
  cd $HOME/tcg-scratch/$tree/crates/trust-cg-verify
  RUST_MIN_STACK=67108864 nice -n 19 $S/testbin_$tag $(cat $S/lib_failing.txt) --exact --test-threads=1 > $S/logs/libcheck_$tag.log 2>&1
  echo "== $tag"; grep -E "^test result" $S/logs/libcheck_$tag.log; grep -E "^test .* FAILED" $S/logs/libcheck_$tag.log | sort -u
done
echo "CHAIN-LIBCHECK-DONE $(date)"
