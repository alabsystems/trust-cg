#!/bin/zsh
# Slice-23 review fixes: apply the rule mutants (reports/.../fails-before/mutate23.py; one build
# serves all, TCG_S23_MUTANT selects), build the mutant library tests (tm), restore the files, then
# run every mutant's controls (fails-before/run_mutants.sh). Every step through build-slot.
F=$HOME/tcg-scratch/s23-fix; W=$HOME/tcg-scratch/wt-s23
R=$W/reports/perf/2026-10-27-darwin-x86-64-slice23-arith-pairing/fails-before
export BUILD_SLOT_MEM_GB=6
step() { echo "$(date +%H:%M:%S) $*" >> $F/logs/chain_mut.txt; }
step START $(git -C $W rev-parse --short HEAD)
[ -z "$(git -C $W status --porcelain -- crates)" ] || { step "worktree crates not clean"; exit 4; }
cp $R/mutate23.py $R/run_mutants.sh $F/
python3 $F/mutate23.py $W >> $F/logs/chain_mut.txt 2>&1 || { step "mutate failed"; git -C $W checkout crates; exit 5; }
$F/build_test.sh tm > $F/logs/build_tm.out 2>&1; RC=$?
git -C $W checkout crates/trust-cg-verify/src/function_request.rs crates/trust-cg-verify/src/x86_source_bound_body.rs crates/trust-cg-verify/src/x86_source_bound_body/normal.rs
step "tm build rc=$RC; restored: $(git -C $W status --porcelain -- crates | wc -l | tr -d ' ') files differ"
[ $RC = 0 ] || exit 6
mkdir -p $F/mutants
zsh $F/run_mutants.sh $W $F/testbin_tm $F/mutants/summary.txt > /dev/null 2>&1
step MUTANTS-DONE
