#!/bin/zsh
# OD-215 lane merged with origin/main e74f215c6: the gates on the merged tree, every build and test
# through build-slot (run.sh: t011 targo --unverified, nice 19, -j2), --no-fail-fast where it applies.
# usage: chain_gates.sh <testbin tag>
TAG=${1:?tag}; M=$HOME/tcg-scratch/i128sh-m1; W=$HOME/tcg-scratch/wt-i128sh
export BUILD_SLOT_MEM_GB=6
step() { echo "$(date +%H:%M:%S) $*" >> $M/logs/chain_gates_$TAG.txt; }
quiet() { while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done; }
step START $(git -C $W rev-parse --short HEAD) dirty=$(git -C $W status --porcelain -- crates | wc -l | tr -d ' ')
# 1. the solver-free x86 body suite
quiet
(cd $W/crates/trust-cg-verify && build-slot -- env RUST_MIN_STACK=67108864 nice -n 19 $M/testbin_$TAG x86_source_bound_body::tests:: \
  --skip host_qualification --skip verifier_credits --skip canonical_migration_pairs --test-threads=2) > $M/logs/suite_$TAG.log 2>&1
step "suite exit=$? $(grep -E '^test result' $M/logs/suite_$TAG.log | tail -1)"
# 2. the tool-gated lanes the fold or the moved goldens touch, one test per process
rm -rf $M/qual_$TAG
zsh $M/qualify.sh $M/testbin_$TAG $M/qual_$TAG \
  x86_source_bound_body::tests::i128_const_shift_qualification::host_qualification_replays_the_i128_const_shift_body_theorems \
  x86_source_bound_body::tests::i128_const_shift_qualification::verifier_credits_every_bound_i128_const_shift_row_with_the_replayed_body_theorem \
  x86_source_bound_body::tests::slice11_qualification::host_qualification_replays_the_slice_eleven_body_theorems \
  x86_source_bound_body::tests::slice11_qualification::verifier_credits_every_bound_slice_eleven_row_with_the_replayed_body_theorem \
  x86_source_bound_body::tests::slice20_qualification::host_qualification_replays_the_slice_twenty_body_theorems \
  x86_source_bound_body::tests::slice20_qualification::host_qualification_refutes_every_slice_twenty_mis_model \
  x86_source_bound_body::tests::slice20_qualification::verifier_credits_every_bound_slice_twenty_row_with_the_replayed_body_theorem \
  x86_source_bound_body::tests::slice23_qualification::host_qualification_replays_the_slice_twenty_three_body_theorems \
  x86_source_bound_body::tests::slice23_qualification::host_qualification_replays_the_slice_twenty_three_generalizations \
  x86_source_bound_body::tests::slice23_qualification::host_qualification_refutes_every_slice_twenty_three_wrong_lowering \
  x86_source_bound_body::tests::slice23_qualification::verifier_credits_every_bound_slice_twenty_three_row_with_the_replayed_body_theorem \
  x86_source_bound_body::tests::host_qualification_verifier_credits_every_bound_row_with_the_replayed_body_theorem \
  x86_source_bound_body::tests::slice10_qualification::verifier_credits_every_bound_slice_ten_row_with_the_replayed_body_theorem \
  x86_source_bound_body::tests::slice14_qualification::verifier_credits_every_bound_slice_fourteen_row_with_the_replayed_body_theorem \
  > $M/logs/qual_$TAG.out 2>&1
step "qualification: $(grep -c 'exit=0' $M/qual_$TAG/summary.txt) passed of $(grep -c 'exit=' $M/qual_$TAG/summary.txt)"
# 3. trust-cg-lower --lib
quiet; rm -rf $HOME/tcg-scratch/stage1-targets/wt-i128sh/debug/incremental
$M/run.sh test -p trust-cg-lower --lib --no-fail-fast -j2 > $M/logs/lower_$TAG.log 2>&1
step "lower --lib exit=$? $(grep -E '^test result' $M/logs/lower_$TAG.log | tr '\n' ' ')"
# 4. codegen
quiet; rm -rf $HOME/tcg-scratch/stage1-targets/wt-i128sh/debug/incremental
$M/run.sh test -p trust-cg-codegen --no-fail-fast -j2 --test x86_source_bound_body --test must_refuse_corpus \
  --test e2e_x86_64_i128_const_shift --test e2e_x86_64_i128_div --test e2e_x86_64_differential \
  --test e2e_x86_64_triple_oracle --test e2e_x86_64_internal_multi_result > $M/logs/codegen_$TAG.log 2>&1
step "codegen exit=$? $(grep -E '^test result|Running' $M/logs/codegen_$TAG.log | tr '\n' ' ')"
# 5. the census proxy on the merged code over core-ir-s23 (ignored test; a diagnostic)
CB=$(grep -o 'Running tests/e2e_x86_64_i128_const_shift.rs ([^)]*)' $M/logs/codegen_$TAG.log | sed 's/.*(\(.*\))/\1/')
if [ -n "$CB" ]; then
  quiet
  (cd $W/crates/trust-cg-codegen && build-slot -- env TCG_I128_CONST_SHIFT_CENSUS_DIR=$HOME/tcg-scratch/runs/core-ir-s23 nice -n 19 $CB \
    --ignored --exact census_proxy_lists_functions_with_a_folded_i128_shift --nocapture) > $M/logs/census_proxy_$TAG.log 2>&1
  step "census proxy exit=$? $(grep I128_CONST_SHIFT_CENSUS_SUMMARY $M/logs/census_proxy_$TAG.log)"
fi
# 6. format, documentation, matrix
(cd $W && TRUST_TARGO="$HOME/Library/Application Support/aterm/pkg/store/trust/6808/bin/targo" bash scripts/check_fmt.sh) > $M/logs/fmt_$TAG.log 2>&1
step "check_fmt exit=$? $(tail -1 $M/logs/fmt_$TAG.log)"
(cd $W && python3 scripts/check_documentation.py --check) > $M/logs/doc_$TAG.log 2>&1
step "check_documentation exit=$? $(tail -1 $M/logs/doc_$TAG.log)"
(cd $W && python3 scripts/full_test_matrix_hosts.py --check) > $M/logs/matrix_$TAG.log 2>&1
R1=$?
(cd $W && TRUST_TARGO="$HOME/Library/Application Support/aterm/pkg/store/trust/6808/bin/targo" python3 scripts/full_test_matrix_hosts.py --check) > $M/logs/matrix6808_$TAG.log 2>&1
step "full_test_matrix_hosts exit=$R1 (PATH) $(tail -1 $M/logs/matrix_$TAG.log); with 6808 TRUST_TARGO exit=$? $(tail -1 $M/logs/matrix6808_$TAG.log)"
step CHAIN-GATES-DONE
