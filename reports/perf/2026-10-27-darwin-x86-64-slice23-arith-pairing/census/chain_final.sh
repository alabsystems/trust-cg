#!/bin/zsh
# Slice 23's final chain on the merged code (each heavy step through build-slot, gated on
# quiet.request by run.sh and the scripts): the solver-free suite on the final test binary, the
# final probe and its whole-core and three-root runs, the codegen and lower gates.
# usage: chain_final.sh <final test binary>
# build-slot admits one job at a time; 6 GiB is the documented memory override (coordinator, 2026-10-27).
export BUILD_SLOT_MEM_GB=6
BIN=${1:?final test binary}; S=$HOME/tcg-scratch/s23-run; W=$HOME/tcg-scratch/wt-s23
quiet() { while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done; }
step() { echo "$(date +%H:%M:%S) $*" >> $S/logs/chain_final.txt; }
step START $(git -C $W rev-parse --short HEAD)
quiet
(cd $W/crates/trust-cg-verify && build-slot -- env RUST_MIN_STACK=67108864 nice -n 19 $BIN x86_source_bound_body::tests:: \
  --skip host_qualification --skip verifier_credits --skip canonical_migration_pairs --test-threads=2) > $S/logs/suite_final.log 2>&1
step "suite exit=$? $(grep -E '^test result' $S/logs/suite_final.log | tail -1)"
$S/probe/build_probe.sh p3 > $S/logs/probe_build_p3.out 2>&1
step "probe p3: $(tail -2 $S/logs/probe_build_p3.out | tr '\n' ' ')"
quiet
build-slot -- zsh $S/probe/run_probe_all.sh $S/probe/x86_body_probe_p3 $HOME/tcg-scratch/runs/core-ir-s23 $S/all/p3 > $S/logs/all_p3.out 2>&1
step "all p3: $(tail -1 $S/logs/all_p3.out)"
$S/probe/run_probe.sh $S/probe/x86_body_probe_p3 $HOME/tcg-scratch/runs/core-ir-s23 $S/probe/names3.txt $S/stage_p3 >> $S/logs/chain_final.txt 2>&1
step "roots p3 done"
$S/run.sh test -p trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus --no-fail-fast > $S/logs/codegen_final.log 2>&1
step "codegen exit=$? $(grep -E '^test result' $S/logs/codegen_final.log | tr '\n' ' ')"
rm -rf $HOME/tcg-scratch/stage1-targets/wt-s23/debug/incremental
$S/run.sh test -p trust-cg-lower --lib --no-fail-fast > $S/logs/lower_final.log 2>&1
step "lower exit=$? $(grep -E '^test result' $S/logs/lower_final.log | tr '\n' ' ')"
step CHAIN-DONE
