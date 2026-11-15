#!/bin/zsh
# OD-215 lane merged with origin/main e74f215c6: slice 23's whole-core probe on the merged tree over
# runs/core-ir-s23, with the fold (m1) and with it off (TCG_NO_X86_I128_CONST_SHIFT=1, m1off), each
# compared with main's run without the fold (s23-fix/all/w5, slice 23's final head 33cb58a2b).
# Every step through build-slot. usage: chain_probe.sh <tag>
TAG=${1:?tag}; M=$HOME/tcg-scratch/i128sh-m1; S=$HOME/tcg-scratch/s23-run
BASE=$HOME/tcg-scratch/s23-fix/all/w5; IR=$HOME/tcg-scratch/runs/core-ir-s23
export BUILD_SLOT_MEM_GB=6
step() { echo "$(date +%H:%M:%S) $*" >> $M/logs/chain_probe_$TAG.txt; }
step START $(git -C $HOME/tcg-scratch/wt-i128sh rev-parse --short HEAD)
rm -rf $HOME/tcg-scratch/stage1-targets/wt-i128sh/debug/incremental
$M/probe/build_probe.sh $TAG > $M/logs/probe_build_$TAG.out 2>&1
[ -x $M/probe/x86_body_probe_$TAG ] || { step "probe build failed"; exit 1; }
step "probe built $(shasum -a 256 $M/probe/x86_body_probe_$TAG | cut -c1-16)"
while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
build-slot -- zsh $S/probe/run_probe_all.sh $M/probe/x86_body_probe_$TAG $IR $M/all/$TAG > $M/logs/all_$TAG.out 2>&1
step "probe $TAG: $(tail -1 $M/logs/all_$TAG.out)"
while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
build-slot -- env TCG_NO_X86_I128_CONST_SHIFT=1 zsh $S/probe/run_probe_all.sh $M/probe/x86_body_probe_$TAG $IR $M/all/${TAG}off > $M/logs/all_${TAG}off.out 2>&1
step "probe ${TAG}off: $(tail -1 $M/logs/all_${TAG}off.out)"
python3 $M/probe/cmp_probe.py $BASE $M/all/$TAG $M/all/cmp_w5_$TAG > $M/all/cmp_w5_$TAG.txt 2>&1
python3 $M/probe/cmp_probe.py $BASE $M/all/${TAG}off $M/all/cmp_w5_${TAG}off > $M/all/cmp_w5_${TAG}off.txt 2>&1
diff -r $BASE/smt2 $M/all/${TAG}off/smt2 > $M/logs/probe_diff_w5_${TAG}off.txt 2>&1; D1=$?
diff $BASE/cf.tsv $M/all/${TAG}off/cf.tsv > /dev/null 2>&1; D2=$?
step "fold on vs w5: $(sed -n 2p $M/all/cmp_w5_$TAG.txt)"
step "fold off vs w5: smt2 diff -r exit=$D1 cf.tsv diff exit=$D2; $(sed -n 2p $M/all/cmp_w5_${TAG}off.txt)"
step "pairing records: on $(grep -c '^S23-PAIRING.*re-derives' $M/all/$TAG/cf.err) re-derive $(grep -c '^S23-PAIRING.*REFUSED' $M/all/$TAG/cf.err) refused; off $(grep -c '^S23-PAIRING.*re-derives' $M/all/${TAG}off/cf.err) re-derive"
step CHAIN-PROBE-DONE
