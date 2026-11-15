#!/bin/zsh
# Slice 23's mutant build and the clean final build, after chain_final.sh's builds are done:
# apply the rule mutants, build the mutant test binary (tm2), restore the files, build the clean
# final test binary (tB3), then run every mutant (through build-slot) and the solver-free suite.
S=$HOME/tcg-scratch/s23-run; W=$HOME/tcg-scratch/wt-s23
export BUILD_SLOT_MEM_GB=6
step() { echo "$(date +%H:%M:%S) $*" >> $S/logs/mutants_final.txt; }
until grep -q 'lower exit' $S/logs/chain_final.txt 2>/dev/null; do
  pgrep -f '[c]hain_final.sh' >/dev/null || { step "chain_final.sh gone without its lower step"; exit 3; }
  sleep 30
done
step START $(git -C $W rev-parse --short HEAD)
[ -z "$(git -C $W status --porcelain -- crates)" ] || { step "worktree crates not clean"; git -C $W status --short >> $S/logs/mutants_final.txt; exit 4; }
python3 $S/fails-before/mutate23.py $W >> $S/logs/mutants_final.txt 2>&1 || { step "mutate failed"; git -C $W checkout crates; exit 5; }
$S/build_test.sh tm2 > $S/logs/build_tm2.out 2>&1
step "tm2: $(head -3 $S/logs/build_tm2.out | tr '\n' ' ')"
git -C $W checkout crates/trust-cg-verify/src/function_request.rs crates/trust-cg-verify/src/x86_source_bound_body.rs crates/trust-cg-verify/src/x86_source_bound_body/normal.rs
step "restored: $(git -C $W status --porcelain -- crates | wc -l | tr -d ' ') files differ"
$S/build_test.sh tB3 > $S/logs/build_tB3.out 2>&1
step "tB3: $(head -3 $S/logs/build_tB3.out | tr '\n' ' ')"
mkdir -p $S/mutants
zsh $S/fails-before/run_mutants.sh $W $S/testbin_tm2 $S/mutants/summary.txt > /dev/null 2>&1
step "mutants done"
(cd $W/crates/trust-cg-verify && build-slot -- env RUST_MIN_STACK=67108864 nice -n 19 $S/testbin_tB3 x86_source_bound_body::tests:: \
  --skip host_qualification --skip verifier_credits --skip canonical_migration_pairs --test-threads=2) > $S/logs/suite_final.log 2>&1
step "suite exit=$? $(grep -E '^test result' $S/logs/suite_final.log | tail -1)"
step MUTANTS-FINAL-DONE
