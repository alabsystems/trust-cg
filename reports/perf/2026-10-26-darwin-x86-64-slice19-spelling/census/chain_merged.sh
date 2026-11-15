#!/bin/zsh
# Slice 19 on origin/main fc03f94f2 (slice 20 landed), one heavy cargo lane, no AY:
# (1) the stage-1 tree's library tests, its goldens re-rendered and pinned; (2) the probe in the
# control tree (main) and each stage's tree; (3) the probe dumps: the 41 roots (stage 3 with its
# claim splits), the seven wide functions, and every function for main and stage 3; (4) the
# stage-2 and stage-3 trees' library tests, their goldens re-rendered and pinned.
# Every build waits on quiet.request (build_probe.sh / build_tests.sh).
S=$HOME/tcg-scratch/s19; T=$HOME/tcg-scratch/stage1-targets/wt-s19
step() { echo "== $1 $(date +%H:%M:%S)"; }
testbin() {  # <tree> <tag>
  $S/build_tests.sh $HOME/tcg-scratch/$1 $S/logs/test_build_$2.log > $S/logs/test_build_$2.out 2>&1
  grep -q "rc=0" $S/logs/test_build_$2.out || { echo "TEST BUILD FAILED $2"; grep -E "^error" -A 6 $S/logs/test_build_$2.log | head -40; exit 1; }
  local bin=$(grep -o "$T/debug/deps/trust_cg_verify-[0-9a-f]*" $S/logs/test_build_$2.log | tail -1)
  cp $bin $S/testbin_$2; echo "testbin_$2 <- $bin"
}
step "test build s1m"; testbin wt-s19 s1m
step "golden write s1m"; $S/golden_write.sh $HOME/tcg-scratch/wt-s19 $S/testbin_s1m $S/logs/golden_write_s1m.log $S/goldens-s1m | tail -20
for st in base20:wt-s19-base s1b:wt-s19 s2b:wt-s19-s2 s3b:wt-s19-s3; do
  tag=${st%%:*}; tree=${st#*:}
  step "probe build $tag"
  $S/build_probe.sh $HOME/tcg-scratch/$tree $S/logs/probe_build_$tag.log $S/probe_$tag > $S/logs/probe_build_$tag.out 2>&1
  grep -q "rc=0" $S/logs/probe_build_$tag.out || { echo "PROBE BUILD FAILED $tag"; grep -E "^error" -A 6 $S/logs/probe_build_$tag.log | head -30; exit 1; }
done
for tag in base20 s1b s2b s3b; do
  while [ -e ~/tcg-scratch/quiet.request ]; do sleep 60; done
  step "probe 41 $tag"
  if [ $tag = s3b ]; then export S19_CLAIMS=1; fi
  $S/run_probe.sh $S/probe_$tag $S/names41.txt $S/redump/$tag
  rm -rf $S/redump/${tag}_mapped $S/redump/${tag}_mapped_claims
  python3 $S/compare_probe.py $S/redump/$tag $S/redump/${tag}_mapped $HOME/tcg-scratch/runs/dump-s20 | tail -3
  unset S19_CLAIMS
done
for tag in base20 s1b s3b; do
  step "probe wide $tag"
  $S/run_probe.sh $S/probe_$tag $S/names_wide.txt $S/redump/wide_$tag
  rm -rf $S/redump/wide_${tag}_mapped
  python3 $S/compare_probe.py $S/redump/wide_$tag $S/redump/wide_${tag}_mapped $HOME/tcg-scratch/runs/dump-s20 | tail -1
done
echo "CHAIN-PROBES-DONE $(date)"
for tag in base20 s3b; do
  while [ -e ~/tcg-scratch/quiet.request ]; do sleep 60; done
  step "probe all $tag"; $S/run_probe_all.sh $S/probe_$tag $S/all/$tag
done
echo "CHAIN-ALL-DONE $(date)"
step "test build s2m"; testbin wt-s19-s2 s2m
step "golden write s2m"; $S/golden_write.sh $HOME/tcg-scratch/wt-s19-s2 $S/testbin_s2m $S/logs/golden_write_s2m.log $S/goldens-s2m | tail -20
step "test build s3m"; testbin wt-s19-s3 s3m
step "golden write s3m"; $S/golden_write.sh $HOME/tcg-scratch/wt-s19-s3 $S/testbin_s3m $S/logs/golden_write_s3m.log $S/goldens-s3m | tail -20
echo "CHAIN-MERGED-DONE $(date)"
