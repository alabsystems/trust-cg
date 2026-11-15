#!/bin/zsh
# Slice 23 on the code merged with origin/main 7cfd635d8 (every build through build-slot, 6 GiB):
# the mutant test binary (tm3), the clean final test binary (tB4), the final probe (p4) with its
# whole-core and three-root runs, the solver-free suite, every mutant, then the full qualification
# one test per process and the deadline-bound lane, the codegen and lower gates.
S=$HOME/tcg-scratch/s23-run; W=$HOME/tcg-scratch/wt-s23
export BUILD_SLOT_MEM_GB=6
step() { echo "$(date +%H:%M:%S) $*" >> $S/logs/final2.txt; }
quiet() { while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done; }
step START $(git -C $W rev-parse --short HEAD)
[ -z "$(git -C $W status --porcelain -- crates)" ] || { step "worktree crates not clean"; exit 4; }
python3 $S/fails-before/mutate23.py $W >> $S/logs/final2.txt 2>&1 || { step "mutate failed"; git -C $W checkout crates; exit 5; }
$S/build_test.sh tm3 > $S/logs/build_tm3.out 2>&1
step "tm3: $(head -3 $S/logs/build_tm3.out | tr '\n' ' ')"
git -C $W checkout crates/trust-cg-verify/src/function_request.rs crates/trust-cg-verify/src/x86_source_bound_body.rs crates/trust-cg-verify/src/x86_source_bound_body/normal.rs
step "restored: $(git -C $W status --porcelain -- crates | wc -l | tr -d ' ') files differ"
$S/build_test.sh tB4 > $S/logs/build_tB4.out 2>&1
step "tB4: $(head -3 $S/logs/build_tB4.out | tr '\n' ' ')"
$S/probe/build_probe.sh p4 > $S/logs/probe_build_p4.out 2>&1
step "probe p4: $(tail -2 $S/logs/probe_build_p4.out | tr '\n' ' ')"
quiet
build-slot -- zsh $S/probe/run_probe_all.sh $S/probe/x86_body_probe_p4 $HOME/tcg-scratch/runs/core-ir-s23 $S/all/p4 > $S/logs/all_p4.out 2>&1
step "all p4: $(tail -1 $S/logs/all_p4.out)"
$S/probe/run_probe.sh $S/probe/x86_body_probe_p4 $HOME/tcg-scratch/runs/core-ir-s23 $S/probe/names3.txt $S/stage_p4 >> $S/logs/final2.txt 2>&1
step "roots p4 done"
quiet
(cd $W/crates/trust-cg-verify && build-slot -- env RUST_MIN_STACK=67108864 nice -n 19 $S/testbin_tB4 x86_source_bound_body::tests:: \
  --skip host_qualification --skip verifier_credits --skip canonical_migration_pairs --test-threads=2) > $S/logs/suite_final.log 2>&1
step "suite exit=$? $(grep -E '^test result' $S/logs/suite_final.log | tail -1)"
mkdir -p $S/mutants3
zsh $S/fails-before/run_mutants.sh $W $S/testbin_tm3 $S/mutants3/summary.txt > /dev/null 2>&1
step "mutants done"
$S/run.sh test -p trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus --no-fail-fast > $S/logs/codegen_final2.log 2>&1
step "codegen exit=$? $(grep -E '^test result' $S/logs/codegen_final2.log | tr '\n' ' ')"
rm -rf $S/qual_final2; mkdir -p $S/qual_final2
zsh $S/census/qualify23.sh $S/testbin_tB4 $S/qual_final2 $(cat $S/census/qual_list.txt) > $S/logs/qual_final2.out 2>&1
quiet
build-slot -- zsh $S/census/qualify_ignored.sh $S/testbin_tB4 $S/qual_final2 >> $S/logs/qual_final2.out 2>&1
step "qualification done: $(grep -c 'exit=0' $S/qual_final2/summary.txt) passed of $(grep -c 'exit=' $S/qual_final2/summary.txt)"
step FINAL2-DONE
