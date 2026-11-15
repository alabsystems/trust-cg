#!/bin/zsh
# OD-224 lane: the release bridge from wt-mulo (build_bridge.t011.sh, through build-slot), a fresh
# trust-ir dump of library/core with it (dump_core_ir.sh, through build-slot: it runs AY on the
# small per-item modules), the dump compared with core-ir-s23 byte for byte, and slice 23's
# whole-core probe (the lane's p4 probe) on the fresh dump in both forms.
M=$HOME/tcg-scratch/mulo-run; W=$HOME/tcg-scratch/wt-mulo; S=$HOME/tcg-scratch/s23-run
export BUILD_SLOT_MEM_GB=6
unset CARGO_TARGET_DIR
step() { echo "$(date +%H:%M:%S) $*" >> $M/logs/chain_bridge.txt; }
step START $(git -C $W rev-parse --short HEAD)
while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
STAMP=$(mktemp); sleep 1
build-slot -- $HOME/tcg-scratch/build_bridge.t011.sh $W > $M/logs/bridge_build.log 2>&1
D=$W/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib
grep -qx "EXIT=0" $M/logs/bridge_build.log && [ -f $D ] && [ $D -nt $STAMP ] || { step "bridge build failed or stale"; exit 3; }
cp $D $M/mulo.dylib; step "bridge built $(shasum -a 256 $M/mulo.dylib | cut -c1-16)"
while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
rm -rf $M/core-ir-mulo $M/core-ir-mulo.obj
build-slot -- $M/dump_core_ir.sh $M/mulo.dylib $M/core-ir-mulo > $M/logs/dump.out 2>&1
step "dump: $(tail -1 $M/logs/dump.out)"
diff -r $HOME/tcg-scratch/runs/core-ir-s23 $M/core-ir-mulo > $M/logs/dump_diff_s23.txt 2>&1; step "dump vs core-ir-s23: diff -r exit=$?"
for FORM in new old; do
  DIV=0; [ $FORM = old ] && DIV=1
  build-slot -- env MULO_DIVISION_FORM=$DIV zsh $S/probe/run_probe_all.sh $M/probe/x86_body_probe_p4 $M/core-ir-mulo $M/all/fresh_$FORM > $M/logs/all_fresh_$FORM.out 2>&1
  diff -r $M/all/p4_$FORM/smt2 $M/all/fresh_$FORM/smt2 > /dev/null 2>&1; A=$?
  diff $M/all/p4_$FORM/cf.tsv $M/all/fresh_$FORM/cf.tsv > /dev/null 2>&1; B=$?
  step "fresh $FORM vs core-ir-s23 $FORM: smt2 diff exit=$A cf.tsv diff exit=$B"
done
python3 $M/probe/cmp_probe.py $M/all/fresh_old $M/all/fresh_new $M/all/cmp_fresh_old_new > $M/all/cmp_fresh_old_new.txt 2>&1
step "fresh new vs old: $(sed -n 2p $M/all/cmp_fresh_old_new.txt)"
step CHAIN-BRIDGE-DONE
