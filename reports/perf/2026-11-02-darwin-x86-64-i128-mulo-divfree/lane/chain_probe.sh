#!/bin/zsh
# OD-224 lane: slice 23's whole-core probe built from wt-mulo, over a core dump, in the division-free
# form (new) and in the division form (old, MULO_DIVISION_FORM=1, = main's adapter); the division
# form compared with main's run (i128sh-m1/all/m1: main 6607d0f6b with OD-215's fold), the two forms
# with each other. Every heavy step through build-slot. usage: chain_probe.sh <tag> <dump dir>
TAG=${1:?tag}; IR=${2:?dump dir}; M=$HOME/tcg-scratch/mulo-run; S=$HOME/tcg-scratch/s23-run
BASE=$HOME/tcg-scratch/i128sh-m1/all/m1
export BUILD_SLOT_MEM_GB=6
step() { echo "$(date +%H:%M:%S) $*" >> $M/logs/chain_probe_$TAG.txt; }
step START $(git -C $HOME/tcg-scratch/wt-mulo rev-parse --short HEAD) dump=$IR
[ -x $M/probe/x86_body_probe_$TAG ] || { rm -rf $HOME/tcg-scratch/stage1-targets/wt-mulo/debug/incremental; $M/probe/build_probe.sh $TAG > $M/logs/probe_build_$TAG.out 2>&1; }
[ -x $M/probe/x86_body_probe_$TAG ] || { step "probe build failed"; exit 1; }
step "probe built $(shasum -a 256 $M/probe/x86_body_probe_$TAG | cut -c1-16)"
for FORM in new old; do
  while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
  DIV=0; [ $FORM = old ] && DIV=1
  build-slot -- env MULO_DIVISION_FORM=$DIV zsh $S/probe/run_probe_all.sh $M/probe/x86_body_probe_$TAG $IR $M/all/${TAG}_$FORM > $M/logs/all_${TAG}_$FORM.out 2>&1
  step "probe $FORM: $(tail -1 $M/logs/all_${TAG}_$FORM.out) $(grep -m1 MULO-PROBE $M/all/${TAG}_$FORM/cf.err)"
done
python3 $M/probe/cmp_probe.py $BASE $M/all/${TAG}_old $M/all/cmp_m1_${TAG}_old > $M/all/cmp_m1_${TAG}_old.txt 2>&1
python3 $M/probe/cmp_probe.py $M/all/${TAG}_old $M/all/${TAG}_new $M/all/cmp_old_new_${TAG} > $M/all/cmp_old_new_${TAG}.txt 2>&1
diff -r $BASE/smt2 $M/all/${TAG}_old/smt2 > $M/logs/probe_diff_m1_${TAG}_old.txt 2>&1; D1=$?
diff $BASE/cf.tsv $M/all/${TAG}_old/cf.tsv > /dev/null 2>&1; D2=$?
step "old vs m1 (main 6607d0f6b with the fold): smt2 diff -r exit=$D1 cf.tsv diff exit=$D2; $(sed -n 2p $M/all/cmp_m1_${TAG}_old.txt)"
step "new vs old: $(sed -n 2p $M/all/cmp_old_new_${TAG}.txt)"
step "pairing records: new $(grep -c '^S23-PAIRING.*re-derives' $M/all/${TAG}_new/cf.err) re-derive $(grep -c '^S23-PAIRING.*REFUSED' $M/all/${TAG}_new/cf.err) refused; old $(grep -c '^S23-PAIRING.*re-derives' $M/all/${TAG}_old/cf.err) re-derive"
step CHAIN-PROBE-DONE
