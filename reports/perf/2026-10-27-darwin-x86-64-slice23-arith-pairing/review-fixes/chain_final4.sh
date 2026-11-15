#!/bin/zsh
# Slice-23 review fixes, re-gated on the code merged with origin/main 451c75834 (the unnamed-module lane):
# the library tests (w4), the solver-free x86 body suite, the codegen and cli gates, the whole-core
# probe (compared byte for byte with 9f7aa5b2b's p4, each paired owner's pairing record
# re-derived on stderr), and the touched qualification lanes one test per process on AY 13556.
# Every step through build-slot. (chain_final.sh is the first merge's, with the lower gate and
# the two lanes under the mutant pair-stamp-only.)
F=$HOME/tcg-scratch/s23-fix; S=$HOME/tcg-scratch/s23-run; W=$HOME/tcg-scratch/wt-s23
Q=$W/reports/perf/2026-10-27-darwin-x86-64-slice23-arith-pairing/census
export BUILD_SLOT_MEM_GB=6
# Post-merge builds use the t011 targo (run.sh beside this script); AY and Clean are AY 13556 and
# Clean 5f09e36c either way.
export RUN=$F/run.sh
step() { echo "$(date +%H:%M:%S) $*" >> $F/logs/chain_final4.txt; }
step START $(git -C $W rev-parse --short HEAD) dirty=$(git -C $W status --porcelain -- crates | wc -l | tr -d ' ')
$F/build_test.sh w4 > $F/logs/build_w4.out 2>&1 || { step "w4 BUILD FAILED"; exit 1; }
step "w4 built"
(cd $W/crates/trust-cg-verify && build-slot -- env RUST_MIN_STACK=67108864 nice -n 19 $F/testbin_w4 x86_source_bound_body::tests:: \
  --skip host_qualification --skip verifier_credits --skip canonical_migration_pairs --test-threads=2) > $F/logs/suite_w4.log 2>&1
step "suite exit=$? $(grep -E '^test result' $F/logs/suite_w4.log | tail -1)"
$RUN test -p trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus --no-fail-fast > $F/logs/codegen_w4.log 2>&1
step "codegen exit=$? $(grep -E '^test result' $F/logs/codegen_w4.log | tr '\n' ' ')"
$RUN test -p trust-cg-cli --bin trust-cg emit_proofs > $F/logs/cli_w4.log 2>&1
step "cli emit_proofs exit=$? $(grep -E '^test result' $F/logs/cli_w4.log | tr '\n' ' ')"
rm -rf $W/../stage1-targets/wt-s23/debug/incremental
PROBE_SRC=$F/probe/x86_body_probe.rs $F/probe/build_probe.sh w4 > $F/logs/probe_build_w4.out 2>&1
[ -x $F/probe/x86_body_probe_w4 ] || { step "probe build failed"; }
build-slot -- zsh $S/probe/run_probe_all.sh $F/probe/x86_body_probe_w4 $HOME/tcg-scratch/runs/core-ir-s23 $F/all/w4 > $F/logs/all_w4.out 2>&1
diff -r $S/all/p4/smt2 $F/all/w4/smt2 > $F/logs/probe_diff_w4.txt 2>&1; D1=$?
diff $S/all/p4/cf.tsv $F/all/w4/cf.tsv > $F/logs/probe_cf_diff_w4.txt 2>&1; D2=$?
step "pairing records on the whole core: $(grep -c "^S23-PAIRING.*re-derives" $F/all/w4/cf.err) re-derive, $(grep -c "^S23-PAIRING.*REFUSED" $F/all/w4/cf.err) refused"
step "probe w4: $(tail -1 $F/logs/all_w4.out); smt2 diff exit=$D1 ($(wc -l < $F/logs/probe_diff_w4.txt) lines), cf.tsv diff exit=$D2, files=$(ls $F/all/w4/smt2 | wc -l | tr -d ' ')"
rm -rf $F/qual_w4; mkdir -p $F/qual_w4
zsh $Q/qualify23.sh $F/testbin_w4 $F/qual_w4 \
  x86_source_bound_body::tests::slice23_qualification::host_qualification_replays_the_slice_twenty_three_body_theorems \
  x86_source_bound_body::tests::slice23_qualification::host_qualification_replays_the_slice_twenty_three_generalizations \
  x86_source_bound_body::tests::slice23_qualification::host_qualification_refutes_every_slice_twenty_three_wrong_lowering \
  x86_source_bound_body::tests::slice23_qualification::verifier_credits_every_bound_slice_twenty_three_row_with_the_replayed_body_theorem \
  x86_source_bound_body::tests::host_qualification_verifier_credits_every_bound_row_with_the_replayed_body_theorem \
  x86_source_bound_body::tests::slice10_qualification::verifier_credits_every_bound_slice_ten_row_with_the_replayed_body_theorem \
  x86_source_bound_body::tests::slice14_qualification::verifier_credits_every_bound_slice_fourteen_row_with_the_replayed_body_theorem \
  > $F/logs/qual_w4.out 2>&1
step "qualification: $(grep -c 'exit=0' $F/qual_w4/summary.txt) passed of $(grep -c 'exit=' $F/qual_w4/summary.txt)"
step CHAIN-FINAL4-DONE
