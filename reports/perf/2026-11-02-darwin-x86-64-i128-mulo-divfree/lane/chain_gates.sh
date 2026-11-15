#!/bin/zsh
# OD-224 lane: the final gates on the lane's head (--no-fail-fast; each heavy step through
# build-slot via run.sh / runbin.sh / qualify.sh).
M=$HOME/tcg-scratch/mulo-run; W=$HOME/tcg-scratch/wt-mulo
step() { echo "$(date +%H:%M:%S) $*" >> $M/logs/chain_gates.txt; }
step START $(git -C $W rev-parse --short HEAD) dirty=$(git -C $W status --porcelain -- crates scripts | wc -l | tr -d ' ')
rm -rf $HOME/tcg-scratch/stage1-targets/wt-mulo/debug/incremental
$M/run.sh test -p trust-cg-lower --lib --no-fail-fast -j2 > $M/logs/gate_lower.log 2>&1
step "lower --lib: $(grep -E '^test result' $M/logs/gate_lower.log | tail -1)"
$M/run.sh test -p trust-cg-verify --lib --no-run -j2 > $M/logs/gate_verify_build.log 2>&1
B=$(grep -o 'Executable unittests src/lib.rs ([^)]*)' $M/logs/gate_verify_build.log | sed 's/.*(\(.*\))/\1/'); cp "$B" $M/testbin_final
step "verify build: $(grep -E '^error|Finished' $M/logs/gate_verify_build.log | tail -1) $(shasum -a 256 $M/testbin_final | cut -c1-16)"
$M/runbin.sh $M/testbin_final x86_source_bound_body::tests:: --skip host_qualification --skip verifier_credits --skip canonical_migration_pairs --test-threads=2 > $M/logs/gate_suite.log 2>&1
step "x86 body suite: $(grep -E '^test result' $M/logs/gate_suite.log | tail -1)"
$M/runbin.sh $M/testbin_final checked_mul_i128_proofs::tests:: --skip formal_attempt --skip structured_formal_attempt --test-threads=2 > $M/logs/gate_l04p10.log 2>&1
step "L04-P10 (solver-free): $(grep -E '^test result' $M/logs/gate_l04p10.log | tail -1)"
mkdir -p $M/qual_final
$M/qualify.sh $M/testbin_final $M/qual_final \
  x86_source_bound_body::tests::i128_mulo_qualification::host_qualification_replays_the_division_free_checked_multiply_theorems \
  x86_source_bound_body::tests::i128_mulo_qualification::host_qualification_refutes_every_division_free_wrong_lowering \
  x86_source_bound_body::tests::i128_mulo_qualification::host_qualification_replays_the_generalizations_of_slice_twenty_two_s_checked_multiplies \
  x86_source_bound_body::tests::slice22_qualification::host_qualification_replays_the_slice_twenty_two_body_theorems \
  x86_source_bound_body::tests::slice22_qualification::host_qualification_refutes_every_slice_twenty_two_wrong_lowering \
  x86_source_bound_body::tests::slice22_qualification::verifier_credits_every_bound_slice_twenty_two_row_with_the_replayed_body_theorem \
  x86_source_bound_body::tests::slice22_qualification::verifier_credits_no_row_whose_routine_the_module_defines \
  checked_mul_i128_proofs::tests::formal_attempt_never_refutes \
  checked_mul_i128_proofs::tests::the_structured_formal_attempt_never_refutes
step "qualification: $(grep -c 'exit=0' $M/qual_final/summary.txt) of $(grep -c 'exit=' $M/qual_final/summary.txt) exit 0"
$M/run.sh test -p trust-cg-verify --no-fail-fast -j2 --test proof_gate_strict --test coverage_gate_tests -- checked_mul_i128 umulh_row > $M/logs/gate_verify_int.log 2>&1
step "proof_gate_strict + coverage_gate_tests: $(grep -E '^test result' $M/logs/gate_verify_int.log | tr '\n' ' ')"
$M/run.sh test -p trust-cg-codegen --lib --no-fail-fast -j2 -- backend_expansion_nounwind_callees > $M/logs/gate_pipeline.log 2>&1
step "pipeline backend_expansion_nounwind_callees: $(grep -E '^test result' $M/logs/gate_pipeline.log | tail -1)"
$M/run.sh test -p trust-cg-codegen --no-fail-fast -j2 --test x86_source_bound_body --test must_refuse_corpus --test e2e_x86_64_i128_div --test e2e_x86_64_checked_arith --test e2e_x86_64_differential --test e2e_x86_64_triple_oracle --test e2e_x86_64_i128_checked_mul > $M/logs/gate_codegen.log 2>&1
step "codegen targets: $(grep -E '^test result' $M/logs/gate_codegen.log | sed 's/; 0 measured.*//' | tr '\n' ' ')"
$M/run.sh test -p trust-cg-codegen -j2 --test e2e_x86_64_i128_checked_mul --test x86_source_bound_body -- --nocapture --test-threads=1 > $M/logs/gate_codegen_nocapture.log 2>&1
step "codegen nocapture: $(grep -E 'I128_MULO_NATIVE|^test result' $M/logs/gate_codegen_nocapture.log | tr '\n' ' ')"
cd $W && TRUST_TARGO="$HOME/Library/Application Support/aterm/pkg/store/trust/6808/bin/targo" bash scripts/check_fmt.sh > $M/logs/gate_fmt.log 2>&1; step "check_fmt exit=$? $(tail -1 $M/logs/gate_fmt.log)"
cd $W && python3 scripts/check_documentation.py --check > $M/logs/gate_doc.log 2>&1; step "check_documentation exit=$? $(tail -1 $M/logs/gate_doc.log)"
cd $W && python3 scripts/full_test_matrix_hosts.py --check > $M/logs/gate_matrix.log 2>&1; step "full_test_matrix_hosts exit=$?"
step CHAIN-GATES-DONE
