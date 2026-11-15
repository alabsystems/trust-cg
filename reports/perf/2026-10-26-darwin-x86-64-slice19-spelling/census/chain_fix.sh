#!/bin/zsh
# The wide-bits rule without products, on the branch tree (wt-s19), after chain_gates.sh:
# (1) the probe and its dumps (the 41 roots with claims, the seven wide functions, every
# function); (2) the library tests and the goldens re-rendered and pinned; (3) the library tests
# rebuilt with those pins. One heavy lane; no AY.
S=$HOME/tcg-scratch/s19; T=$HOME/tcg-scratch/stage1-targets/wt-s19; W=$HOME/tcg-scratch/wt-s19
until grep -q "CHAIN-GATES-DONE" $S/logs/chain_gates.log 2>/dev/null || ! pgrep -f "[c]hain_gates.sh" >/dev/null; do sleep 20; done
testbin() {  # <tree> <tag>
  $S/build_tests.sh $1 $S/logs/test_build_$2.log > $S/logs/test_build_$2.out 2>&1
  grep -q "rc=0" $S/logs/test_build_$2.out || { echo "TEST BUILD FAILED $2"; grep -E "^error" -A 8 $S/logs/test_build_$2.log | head -60; exit 1; }
  local bin=$(grep -o "$T/debug/deps/trust_cg_verify-[0-9a-f]*" $S/logs/test_build_$2.log | tail -1)
  cp $bin $S/testbin_$2; echo "testbin_$2 <- $bin"
}
echo "== probe build s3c $(date +%H:%M)"
$S/build_probe.sh $W $S/logs/probe_build_s3c.log $S/probe_s3c > $S/logs/probe_build_s3c.out 2>&1
grep -q "rc=0" $S/logs/probe_build_s3c.out || { echo "PROBE BUILD FAILED s3c"; exit 1; }
echo "== probes s3c $(date +%H:%M)"
S19_CLAIMS=1 $S/run_probe.sh $S/probe_s3c $S/names41.txt $S/redump/s3c
rm -rf $S/redump/s3c_mapped $S/redump/s3c_mapped_claims
python3 $S/compare_probe.py $S/redump/s3c $S/redump/s3c_mapped $S/redump/s3b_mapped | head -3
$S/run_probe.sh $S/probe_s3c $S/names_wide.txt $S/redump/wide_s3c
rm -rf $S/redump/wide_s3c_mapped; python3 $S/compare_probe.py $S/redump/wide_s3c $S/redump/wide_s3c_mapped $S/redump/wide_s3b_mapped | head -1
echo "CHAIN-FIX-PROBES-DONE $(date)"
echo "== test build final2 $(date +%H:%M)"; testbin $W final2
echo "== golden write final2 $(date +%H:%M)"
$S/golden_write.sh $W $S/testbin_final2 $S/logs/golden_write_final2.log $S/goldens-final2 | tail -20
echo "== test build final3 $(date +%H:%M)"; testbin $W final3
echo "== probe all s3c $(date +%H:%M)"; $S/run_probe_all.sh $S/probe_s3c $S/all/s3c
echo "CHAIN-FIX-DONE $(date)"
