#!/bin/zsh
# After chain_merged.sh's probes (CHAIN-ALL-DONE): stop it before its stage-2 test build (stage 3
# does not change the spelling, so stage 3's goldens are stage 2's), then (1) the stage-3 tree's
# library tests and its goldens re-rendered and pinned; (2) the mutant tree: the stage-3 tree's
# changes over main with those goldens, every remaining mutant applied (mutate19.py all), one
# test build; (3) the mutant runs over each stage's controls. One heavy lane; no AY.
S=$HOME/tcg-scratch/s19; T=$HOME/tcg-scratch/stage1-targets/wt-s19; M=$HOME/tcg-scratch/wt-s19-mut
until grep -q "CHAIN-ALL-DONE" $S/logs/chain_merged.log 2>/dev/null || ! pgrep -f "[c]hain_merged.sh" >/dev/null; do sleep 20; done
pkill -f "[c]hain_merged.sh"; sleep 2; pkill -f "[b]uild_tests.sh $HOME/tcg-scratch/wt-s19-s2"; sleep 2
pkill -f "[t]argo --unverified test -p trust-cg-verify --lib --no-run"; sleep 2
grep -q "CHAIN-ALL-DONE" $S/logs/chain_merged.log || { echo "chain_merged died before its probes"; exit 1; }
testbin() {  # <tree> <tag>
  $S/build_tests.sh $1 $S/logs/test_build_$2.log > $S/logs/test_build_$2.out 2>&1
  grep -q "rc=0" $S/logs/test_build_$2.out || { echo "TEST BUILD FAILED $2"; grep -E "^error" -A 8 $S/logs/test_build_$2.log | head -60; exit 1; }
  local bin=$(grep -o "$T/debug/deps/trust_cg_verify-[0-9a-f]*" $S/logs/test_build_$2.log | tail -1)
  cp $bin $S/testbin_$2; echo "testbin_$2 <- $bin"
}
echo "== test build s3m $(date +%H:%M)"; testbin $HOME/tcg-scratch/wt-s19-s3 s3m
echo "== golden write s3m $(date +%H:%M)"
$S/golden_write.sh $HOME/tcg-scratch/wt-s19-s3 $S/testbin_s3m $S/logs/golden_write_s3m.log $S/goldens-s3m | tail -20
echo "== mutant tree $(date +%H:%M)"
cd $M || exit 9
git checkout -q -- . && git clean -qfd crates docs 2>/dev/null
git checkout -q --detach origin/main || exit 9
cd $HOME/tcg-scratch/wt-s19-s3
for f in $(git status --short | awk '{print $2}'); do mkdir -p $M/$(dirname $f); cp -R $f $M/$f; done
cd $M; git status --short | wc -l
python3 $S/fails-before/mutate19.py $M all > $S/logs/mutate_all.txt || { echo "MUTATE FAILED"; cat $S/logs/mutate_all.txt; exit 1; }
echo "== mutant build $(date +%H:%M)"; testbin $M mutall
echo "CHAIN-POST-DONE $(date)"
