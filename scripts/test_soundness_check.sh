#!/usr/bin/env bash
#
# Focused regressions for soundness_check.sh's command dispatch, non-vacuity,
# Clean command, dependency-lock, fail-fast and finalization controls. This does
# not run the cross-repository soundness constellation.
# --finalization-only runs the shell-only summary/attest/oracle, pre-push hook
# and Git-environment controls.
#
set -u
set -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")/.." && pwd)"
SOUNDNESS_CHECK="${ROOT}/scripts/soundness_check.sh"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/test_soundness_check.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT HUP INT TERM

PASS=0
FAIL=0
ok() { printf 'ok - %s\n' "$1"; PASS=$((PASS + 1)); }
not_ok() { printf 'not ok - %s\n' "$1" >&2; FAIL=$((FAIL + 1)); }

# Execute the production finalization functions, not a test-local
# reimplementation of their policy. Only earlier gate outcomes and the
# attestation tool are synthetic: the tool stub records its argv, so the test
# sees whether a record would be built and written.
FINALIZATION_FIXTURE="${TMP}/finalization"
mkdir -p "$FINALIZATION_FIXTURE"
awk '/^# Summary\. finish_run/ { active=1 } /^# End of summary\.$/ { active=0 } active { print }' \
  "$SOUNDNESS_CHECK" >"$FINALIZATION_FIXTURE/summary.sh"
awk '/^record\(\) \{$/ { active=1 } active { print } active && /^}$/ { exit }' \
  "$SOUNDNESS_CHECK" >"$FINALIZATION_FIXTURE/record.sh"
awk '
  /^# Single-gate lane:/ { active=1 }
  /^# Banner \+ preflight\.$/ { active=0 }
  active { print }
' "$SOUNDNESS_CHECK" >"$FINALIZATION_FIXTURE/oracle.sh"
grep -q '^finish_run() {' "$FINALIZATION_FIXTURE/summary.sh" || { echo 'summary block not found' >&2; exit 1; }
grep -q 'finish_run' "$FINALIZATION_FIXTURE/record.sh" || { echo 'record() does not stop a fail-fast run' >&2; exit 1; }
cat >"$FINALIZATION_FIXTURE/tool.py" <<'EOF'
import os, sys
with open(os.environ["TOOL_LOG"], "a") as log:
    log.write(" ".join(sys.argv[1:3]) + "\n")
if sys.argv[1] == os.environ.get("TOOL_REFUSES", ""):
    print("refused: fixture")
    sys.exit(1)
if sys.argv[1] == "write":
    print("wrote refs/attest/soundness/fixture/fixture-host -> " + "a" * 40)
    print("a" * 40)
EOF
cat >"$FINALIZATION_FIXTURE/driver.sh" <<'EOF'
#!/usr/bin/env bash
set -u
set -o pipefail
fixture_dir="$1" mode="$2" outcome="$3"
C_GRN='' C_RED='' C_YEL='' C_RST='' C_BLD=''
PASS_COUNT=1 FAIL_COUNT=0 SKIP_COUNT=0
GATE_NAMES=('synthetic gate') GATE_STATUS=(PASS) GATE_DETAIL=('synthetic evidence')
case "$outcome" in
  pass) ;;
  fail) FAIL_COUNT=1; GATE_STATUS+=(FAIL); GATE_NAMES+=(failure); GATE_DETAIL+=(fixture) ;;
  skip) SKIP_COUNT=1; GATE_STATUS+=(SKIP); GATE_NAMES+=(missing); GATE_DETAIL+=(fixture) ;;
  fail-skip) FAIL_COUNT=1; SKIP_COUNT=1; GATE_STATUS+=(FAIL SKIP); GATE_NAMES+=(failure missing); GATE_DETAIL+=(fixture fixture) ;;
  preflight-red) ;;
  *) exit 96 ;;
esac
MODE_ATTEST=0 MODE_PREFLIGHT_ONLY=0 MODE_RUN_WASM_ORACLES=0 RUN_SCOPE=full
case "$mode" in
  normal) ;;
  attest) MODE_ATTEST=1 ;;
  attest-x86) MODE_ATTEST=1; RUN_SCOPE=x86_64-native ;;
  preflight-only) MODE_ATTEST=1; MODE_PREFLIGHT_ONLY=1 ;;
  oracle) MODE_RUN_WASM_ORACLES=1 ;;
  *) exit 97 ;;
esac
TRUST_CG_DIR=synthetic-cg CLEAN_BIN=synthetic-clean-bin
LOGDIR="$fixture_dir" ATTESTATION_TOOL="$fixture_dir/tool.py"
WASM_CFG_FUZZ_FUNCS=200
# The gate's pinned interpreter (OD-XHOST-GATE-CWD-20261025, repair round 3):
# the production finalization starts the attestation tool by it.
SOUNDNESS_PYTHON3="$(type -P python3)"
hr() { :; }
section() { printf '%s\n' "$*"; }
run_wasm_oracle_gate() { :; }
run_island_gates() { :; }
if [ "$mode" = oracle ]; then
  source "$fixture_dir/oracle.sh"
else
  source "$fixture_dir/summary.sh"
  RUN_STARTED_AT=fixture-start START_TRUST_HEAD=fixture-head
  [ "$outcome" != preflight-red ] || PREFLIGHT_OK=0
  finish_run
fi
# Every production finalization must actually terminate the process.
echo 'fixture finalization unexpectedly returned' >&2
exit 98
EOF

finalization_case() {
  # finalization_case <mode> <outcome> <refusing tool subcommand or ''>
  local mode="$1" outcome="$2" refuses="${3:-}" output rc ok=1 calls
  : >"$FINALIZATION_FIXTURE/tool.log"
  output="$(TOOL_LOG="$FINALIZATION_FIXTURE/tool.log" TOOL_REFUSES="$refuses" \
    bash "$FINALIZATION_FIXTURE/driver.sh" "$FINALIZATION_FIXTURE" "$mode" "$outcome" 2>&1)"
  rc=$?
  calls="$(tr '\n' ',' <"$FINALIZATION_FIXTURE/tool.log")"
  if [ "$outcome" = pass ] && [ -z "$refuses" ]; then
    [ "$rc" -eq 0 ] || ok=0
    case "$mode" in
      normal)
        printf '%s\n' "$output" | grep -Fq 'ALL SOUNDNESS GATES GREEN.' || ok=0
        [ -z "$calls" ] || ok=0 ;;
      attest|attest-x86)
        printf '%s\n' "$output" | grep -Fq 'ALL SOUNDNESS GATES GREEN.' || ok=0
        [ "$calls" = "build --repo,write --repo," ] || ok=0
        printf '%s\n' "$output" | grep -Fq 'wrote refs/attest/soundness/' || ok=0
        if [ "$mode" = attest ]; then
          grep -Fq 'build --repo' "$FINALIZATION_FIXTURE/tool.log" || ok=0
        fi ;;
      preflight-only)
        printf '%s\n' "$output" | grep -Fq 'PREFLIGHT GREEN' || ok=0
        ! printf '%s\n' "$output" | grep -Fq 'ALL SOUNDNESS GATES GREEN.' || ok=0
        [ -z "$calls" ] || ok=0 ;;
    esac
  else
    [ "$rc" -eq 1 ] || ok=0
    ! printf '%s\n' "$output" | grep -Fq 'ALL SOUNDNESS GATES GREEN.' || [ -n "$refuses" ] || ok=0
    ! printf '%s\n' "$output" | grep -Fq 'PREFLIGHT GREEN' || ok=0
    if [ -n "$refuses" ]; then
      printf '%s\n' "$output" | grep -Eq 'refusing to write|record was not written' || ok=0
    elif [ "$mode" != normal ] && [ "$mode" != oracle ]; then
      [ -z "$calls" ] || ok=0
      [ "$mode" = preflight-only ] || printf '%s\n' "$output" | grep -Fq 'no attestation record' || ok=0
    fi
    case "$outcome" in
      *skip*) printf '%s\n' "$output" | grep -Fq 'SKIPPED' || ok=0 ;;
    esac
  fi
  if [ "$ok" -eq 1 ]; then
    ok "production ${mode} finalization with ${outcome}${refuses:+ (tool refuses $refuses)}"
  else
    not_ok "production ${mode} finalization with ${outcome}${refuses:+ (tool refuses $refuses)} (rc=${rc}, calls=${calls}, output: ${output})"
  fi
}
for finalization_mode in normal attest attest-x86 preflight-only oracle; do
  for finalization_outcome in pass fail skip fail-skip; do
    finalization_case "$finalization_mode" "$finalization_outcome"
  done
done
for finalization_mode in normal attest preflight-only; do
  finalization_case "$finalization_mode" preflight-red
done
finalization_case attest pass build
finalization_case attest pass write

# Fail-fast: the production record() stops an --attest run at the first
# non-PASS leg (finish_run is the only exit), but never during the preflight,
# whose rows are all recorded before the run stops.
cat >"$FINALIZATION_FIXTURE/failfast.sh" <<'EOF'
set -u
C_GRN='' C_RED='' C_YEL='' C_RST='' C_BLD=''
GATE_NAMES=() GATE_STATUS=() GATE_DETAIL=() PASS_COUNT=0 FAIL_COUNT=0 SKIP_COUNT=0
LEGS_TSV="$1/legs.tsv" LAST_RECORD_SECONDS=$SECONDS
: >"$LEGS_TSV"
source "$1/record.sh"
finish_run() { echo "FINISHED at ${STOPPED_AT:-}"; exit 1; }
FAIL_FAST="$2" RUN_PHASE="$3"
record "first leg" PASS "fine" "$1/first.log"
record "second leg" FAIL "red"
record "third leg" PASS "must not run under fail-fast in the legs phase"
echo "RAN TO THE END"
EOF
for failfast_case in "1 legs stop" "1 preflight continue" "0 legs continue"; do
  read -r ff_flag ff_phase ff_expect <<<"$failfast_case"
  output="$(bash "$FINALIZATION_FIXTURE/failfast.sh" "$FINALIZATION_FIXTURE" "$ff_flag" "$ff_phase" 2>&1)"
  rc=$?
  tsv_rows="$(wc -l <"$FINALIZATION_FIXTURE/legs.tsv" | tr -d ' ')"
  if [ "$ff_expect" = stop ] && [ "$rc" -eq 1 ] && printf '%s\n' "$output" | grep -Fq 'FINISHED at second leg' && \
     ! printf '%s\n' "$output" | grep -Fq 'third leg' && [ "$tsv_rows" -eq 2 ] && \
     grep -Fq "$(printf 'first leg\tPASS\t')" "$FINALIZATION_FIXTURE/legs.tsv"; then
    ok "record() stops a fail-fast run at the first failing leg"
  elif [ "$ff_expect" = continue ] && [ "$rc" -eq 0 ] && printf '%s\n' "$output" | grep -Fq 'RAN TO THE END' && \
     [ "$tsv_rows" -eq 3 ]; then
    ok "record() continues (fail-fast=$ff_flag, phase $ff_phase)"
  else
    not_ok "record() fail-fast=$ff_flag phase=$ff_phase (rc=$rc, rows=$tsv_rows, output: $output)"
  fi
done

# The retired lock modes name their replacement and run nothing.
for retired in --pinned --update; do
  output="$(bash "$SOUNDNESS_CHECK" "$retired" 2>&1)"
  rc=$?
  if [ "$rc" -eq 2 ] && printf '%s\n' "$output" | grep -Fq 'use --attest'; then
    ok "retired $retired exits 2 and names --attest"
  else
    not_ok "retired $retired (rc=$rc, output: $output)"
  fi
done
for bad in "--preflight-only" "--host-legs x86_64-native" "--host-legs aarch64" "--attest --list-json"; do
  # shellcheck disable=SC2086
  output="$(bash "$SOUNDNESS_CHECK" $bad 2>&1)"
  rc=$?
  if [ "$rc" -eq 2 ]; then
    ok "invalid mode combination refused: $bad"
  else
    not_ok "invalid mode combination $bad (rc=$rc, output: $output)"
  fi
done

if bash "$ROOT/scripts/test_pre_push_hook.sh"; then
  PASS=$((PASS + 1))
else
  FAIL=$((FAIL + 1))
fi
if bash "$ROOT/scripts/test_soundness_git_environment.sh"; then
  PASS=$((PASS + 1))
else
  FAIL=$((FAIL + 1))
fi
if [ "${1:-}" = --finalization-only ]; then
  printf '%d passed, %d failed\n' "$PASS" "$FAIL"
  [ "$FAIL" -eq 0 ]
  exit $?
fi

accepts() {
  local name="$1" contents="$2" expected="$3"
  local log="${TMP}/${name}.log"
  local output
  printf '%s' "$contents" >"$log"
  if output="$("$SOUNDNESS_CHECK" --validate-clean-summary "$log" 2>&1)" && \
     [ "$output" = "$expected" ]; then
    printf 'ok - accepts %s\n' "$name"
    PASS=$((PASS + 1))
  else
    printf 'not ok - accepts %s (output: %s)\n' "$name" "${output:-<empty>}" >&2
    FAIL=$((FAIL + 1))
  fi
}

rejects() {
  local name="$1" contents="$2"
  local log="${TMP}/${name}.log"
  local output
  printf '%s' "$contents" >"$log"
  if output="$("$SOUNDNESS_CHECK" --validate-clean-summary "$log" 2>&1)"; then
    printf 'not ok - rejects %s (unexpected success: %s)\n' "$name" "$output" >&2
    FAIL=$((FAIL + 1))
  else
    printf 'ok - rejects %s\n' "$name"
    PASS=$((PASS + 1))
  fi
}

accepts \
  valid_241 \
  $'Loading proof...\nChecked 241 declarations in 1.038183542s\n  241 passed, 0 failed\n' \
  'Checked 241 declarations; 241 passed, 0 failed'

rejects empty_rc0 ''
rejects zero_zero $'Checked 0 declarations in 1ms\n  0 passed, 0 failed\n'
rejects mismatch $'Checked 241 declarations in 1ms\n  240 passed, 0 failed\n'
rejects failed $'Checked 241 declarations in 1ms\n  240 passed, 1 failed\n'
rejects malformed $'Checked: 241 declarations\n  241 passed / 0 failed\n'
rejects duplicate_summaries \
  $'Checked 241 declarations in 1ms\n  241 passed, 0 failed\nChecked 241 declarations in 1ms\n  241 passed, 0 failed\n'
rejects duplicate_checked \
  $'Checked 241 declarations in 1ms\nChecked 241 declarations in 2ms\n  241 passed, 0 failed\n'
rejects duplicate_result \
  $'Checked 241 declarations in 1ms\n  241 passed, 0 failed\n  241 passed, 0 failed\n'

# Run the actual shared Cargo inventory/helper. Only the fixture checkout's
# timeout wrapper is a test double: it records the production argv and returns
# a selected process outcome. No Rust compilation, environment bypass in the
# production script, or reassignment of HOME is needed for these controls.
# A space in the fixture path also checks the bounded runner's argument quoting.
CARGO_GATE_FIXTURE="${TMP}/cargo gate fixture"
mkdir -p "$CARGO_GATE_FIXTURE/scripts" "$CARGO_GATE_FIXTURE/logs"
cp "$(dirname "$SOUNDNESS_CHECK")/matrix_results.py" "$CARGO_GATE_FIXTURE/scripts/matrix_results.py"
# The gate starts its bounded runner as `python3 -I <runner>`
# (OD-XHOST-GATE-CWD-20261025): the double is a Python script that hands its
# argv to the bash double beside it.
cat >"$CARGO_GATE_FIXTURE/scripts/run_with_timeout.py" <<'EOF'
#!/usr/bin/env python3
import os
import sys
double = os.path.join(os.path.dirname(os.path.abspath(__file__)), "run_with_timeout.double.sh")
os.execv("/usr/bin/env", ["env", "bash", double, *sys.argv[1:]])
EOF
cat >"$CARGO_GATE_FIXTURE/scripts/run_with_timeout.double.sh" <<'EOF'
#!/usr/bin/env bash
set -u
if [ "$#" -lt 10 ] || [ "$1" != --chdir ] || [ "$3" != 17 ]; then
  echo 'unexpected bounded-runner arguments' >&2
  exit 98
fi
fixture_dir="$2"
printf '%s\t' "$@" >>"$fixture_dir/argv.log"
printf '\n' >>"$fixture_dir/argv.log"
shift 3
selector="${6}|${7}"
fault_selector="$(<"$fixture_dir/fault.selector")"
fault_kind="$(<"$fixture_dir/fault.kind")"
if [ "$selector" = "$fault_selector" ]; then
  case "$fault_kind" in
    zero) echo 'test result: ok. 0 passed; 0 failed; 1 filtered out'; exit 0 ;;
    empty) exit 0 ;;
    failed) echo 'test result: FAILED. 1 passed; 1 failed'; exit 101 ;;
    failed-rc0) echo 'test result: FAILED. 1 passed; 1 failed'; exit 0 ;;
    missing-count) echo 'test result: ok. no passing count'; exit 0 ;;
    not-ok) echo 'test result: not ok. 1 passed; 0 failed'; exit 0 ;;
    contradictory) echo 'test result: ok. 1 passed; 1 failed'; exit 0 ;;
    build) echo 'error: fixture compile failure'; exit 101 ;;
    timeout) exit 124 ;;
    nonzero-ok) echo 'test result: ok. 1 passed; 0 failed'; exit 1 ;;
    ten)
      echo 'running 10 tests'
      for i in {1..10}; do echo "test witness_$i ... ok"; done
      echo 'test result: ok. 10 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;'
      exit 0 ;;
    *) echo 'unknown fixture outcome' >&2; exit 99 ;;
  esac
fi
echo 'running 1 test'
echo 'test witness ... ok'
echo 'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;'
EOF
chmod +x "$CARGO_GATE_FIXTURE/scripts/run_with_timeout.py"

cargo_gate_output=""
cargo_gate_rc=0
run_cargo_fixture() {
  printf '%s\n' "$1" >"$CARGO_GATE_FIXTURE/fault.selector"
  printf '%s\n' "$2" >"$CARGO_GATE_FIXTURE/fault.kind"
  : >"$CARGO_GATE_FIXTURE/argv.log"
  cargo_gate_output="$(
    TRUST_CG_DIR="$CARGO_GATE_FIXTURE" \
    TMPDIR="$CARGO_GATE_FIXTURE/logs" \
    SOUNDNESS_COMMAND_TIMEOUT_SECONDS=17 \
      "$SOUNDNESS_CHECK" --self-test-cargo-gates 2>&1
  )"
  cargo_gate_rc=$?
}

# Derive expected dispatch from --list, then require the security-relevant
# inventory explicitly as well: list and execution agreeing on a deleted gate
# must not make the regression pass. No test-count expectations are pinned.
"$SOUNDNESS_CHECK" --list >"$CARGO_GATE_FIXTURE/list.log"
awk '
  /^trust-cg gate test targets / { active=1; next }
  active && /^  - / { print $2; next }
  active { exit }
' "$CARGO_GATE_FIXTURE/list.log" >"$CARGO_GATE_FIXTURE/integration.list"
awk '
  /^trust-cg release-mode gate test targets / { active=1; next }
  active && /^  - / { print $2; next }
  active { exit }
' "$CARGO_GATE_FIXTURE/list.log" >"$CARGO_GATE_FIXTURE/release.list"
awk '
  /^trust-cg library gates / { active=1; next }
  active && /^  - / { print $2 "|" $4; next }
  active { exit }
' "$CARGO_GATE_FIXTURE/list.log" >"$CARGO_GATE_FIXTURE/library.list"
awk '
  /^trust-cg package integration gates / { active=1; next }
  active && /^  - / { print $2 "|" $4; next }
  active { exit }
' "$CARGO_GATE_FIXTURE/list.log" >"$CARGO_GATE_FIXTURE/package_integration.list"
# WS7.1 (F-111): the value-semantic InsertField lowering and the store-form
# refusal on the CLI are whole integration targets outside trust-cg-verify;
# so are WS7.3's (F-113) ingestion admission and the license tests beside it.
required_package_integration_gates=(
  'trust-cg-codegen|aarch64_framed_identity_control'
  'trust-cg-codegen|aarch64_nonleaf_frame_control'
  'trust-cg-codegen|insert_field_value_semantics'
  'trust-cg-cli|insert_field_store_form'
  'trust-cg-codegen|ingest_admission'
  'trust-cg-codegen|v41_abi_residue_objects'
  'trust-cg-codegen|aarch64_elf_symbol_binding'
  'trust-cg-codegen|x86_source_bound_body'
)
required_lib_gates=(
  'trust-cg-verify|tv2_'
  'trust-cg-verify|coverage_gate::'
  'trust-cg-verify|source_bound_frame::tests::framed_control_'
  'trust-cg-verify|source_bound_a64_body::tests::pure_jump_cycle_binds_forward_and_negative_decoded_displacements'
  'trust-cg-codegen|affine_lowering_tests'
  'trust-cg-codegen|verification_precondition'
  'trust-cg-codegen|jit_cert::tests::'
  'trust-cg-codegen|test_generate_proof_certificates_rejects'
  'trust-cg-codegen|x86_authoritative_'
  'trust-cg-verify|checked_mul_i128_proofs::tests::credit_'
  'trust-cg-verify|x86_source_bound_body::tests::slice5::'
  'trust-cg-verify|x86_source_bound_body::tests::slice6::'
  'trust-cg-verify|x86_source_bound_body::tests::slice7::'
  'trust-cg-verify|x86_source_bound_body::tests::slice9::'
  'trust-cg-verify|x86_source_bound_body::tests::slice10::'
  'trust-cg-verify|x86_source_bound_body::tests::slice11::'
  'trust-cg-verify|x86_source_bound_body::tests::slice12::'
  'trust-cg-verify|x86_source_bound_body::tests::slice13::'
  'trust-cg-verify|x86_source_bound_body::tests::slice14::'
  'trust-cg-verify|x86_source_bound_body::tests::slice15::'
  'trust-cg-verify|x86_source_bound_body::tests::slice16::'
  'trust-cg-verify|x86_source_bound_body::tests::qualification_matrix::'
  'trust-cg-verify|source_bound_negative_memo::'
  'trust-cg-verify|x86_source_bound_body::tests::negative_memo::'
)
inventory_ok=1
grep -Fxq aarch64_affine_lowering "$CARGO_GATE_FIXTURE/integration.list" || inventory_ok=0
grep -Fxq aarch64_trust_ir_affine_lowering "$CARGO_GATE_FIXTURE/integration.list" || inventory_ok=0
grep -Fxq x86_encoding_gate "$CARGO_GATE_FIXTURE/integration.list" || inventory_ok=0
grep -Fxq x86_sse_lane_gate "$CARGO_GATE_FIXTURE/integration.list" || inventory_ok=0
grep -Fxq x86_movsxd_sib_gate "$CARGO_GATE_FIXTURE/integration.list" || inventory_ok=0
# The release-mode set must be PUBLISHED and non-empty. Without this, deleting
# the --list section would leave `release.list` empty, every gate would expect
# the debug argv, and the check below would agree with a broken script.
[ -s "$CARGO_GATE_FIXTURE/release.list" ] || inventory_ok=0
for release_gate in wasm_encoding_gate x86_encoding_gate x86_sse_lane_gate x86_movsxd_sib_gate; do
  grep -Fxq "$release_gate" "$CARGO_GATE_FIXTURE/release.list" || inventory_ok=0
done
for cargo_gate in "${required_lib_gates[@]}"; do
  grep -Fxq "$cargo_gate" "$CARGO_GATE_FIXTURE/library.list" || inventory_ok=0
done
grep -Fxq '  - trust-cg-lower --lib lattice_guard::tests:: --features lattice-guard-elision' "$CARGO_GATE_FIXTURE/list.log" || inventory_ok=0
grep -Fxq '  - trust-cg-codegen --test a64_lattice_guard_elision_differential --features lattice-guard-elision' "$CARGO_GATE_FIXTURE/list.log" || inventory_ok=0
grep -Fxq '  - trust-cg-lower --test refine_erasure_hazards' "$CARGO_GATE_FIXTURE/list.log" || inventory_ok=0
grep -Fxq '  - trust-cg-codegen --test a64_refine_byte_invariance' "$CARGO_GATE_FIXTURE/list.log" || inventory_ok=0
for cargo_gate in "${required_package_integration_gates[@]}"; do
  grep -Fxq "$cargo_gate" "$CARGO_GATE_FIXTURE/package_integration.list" || inventory_ok=0
done
if [ "$inventory_ok" -eq 1 ]; then
  printf 'ok - required independent lowering and source-authority gates are listed\n'
  PASS=$((PASS + 1))
else
  printf 'not ok - required Cargo gate missing from --list\n' >&2
  FAIL=$((FAIL + 1))
fi

# Every gate runs through the Trust wrapper (targo --unverified; the proof
# campaign's AY comes from the Trust sysroot that builds trust-cg-verify).
expected_cargo_argv() {
  printf '%s\t' --chdir "$CARGO_GATE_FIXTURE" 17 "$CARGO_GATE_FIXTURE/scripts/trust_cargo.sh" \
    test --locked -p "$@"
  printf '\n'
}
{
  while IFS= read -r cargo_gate; do
    if grep -Fxq "$cargo_gate" "$CARGO_GATE_FIXTURE/release.list"; then
      expected_cargo_argv trust-cg-verify --test "$cargo_gate" --release -- --show-output --include-ignored
    else
      expected_cargo_argv trust-cg-verify --test "$cargo_gate" -- --show-output
    fi
  done <"$CARGO_GATE_FIXTURE/integration.list"
  while IFS='|' read -r cargo_pkg cargo_filter; do
    expected_cargo_argv "$cargo_pkg" --lib "$cargo_filter" -- --show-output --test-threads=1
  done <"$CARGO_GATE_FIXTURE/library.list"
  expected_cargo_argv trust-cg-lower --lib lattice_guard::tests:: --features lattice-guard-elision -- --show-output --test-threads=1
  expected_cargo_argv trust-cg-codegen --test a64_lattice_guard_elision_differential --features lattice-guard-elision -- --show-output
  expected_cargo_argv trust-cg-lower --test refine_erasure_hazards -- --show-output
  expected_cargo_argv trust-cg-codegen --test a64_refine_byte_invariance -- --show-output
  expected_cargo_argv trust-cg-llvm-import --test c_string_escapes_e2e --features driver -- --show-output
  while IFS='|' read -r cargo_pkg cargo_target; do
    expected_cargo_argv "$cargo_pkg" --test "$cargo_target" -- --show-output
  done <"$CARGO_GATE_FIXTURE/package_integration.list"
} >"$CARGO_GATE_FIXTURE/expected.argv"

run_cargo_fixture none none
if [ "$cargo_gate_rc" -eq 0 ] && \
   [ -s "$CARGO_GATE_FIXTURE/expected.argv" ] && \
   cmp -s "$CARGO_GATE_FIXTURE/expected.argv" "$CARGO_GATE_FIXTURE/argv.log" && \
   grep -Fq 'no cross-repository preflight; NOT an attestation record.' <<< "$cargo_gate_output"; then
  printf 'ok - shared Cargo inventory dispatches exact bounded integration/library argv\n'
  PASS=$((PASS + 1))
else
  printf 'not ok - shared Cargo dispatch (rc=%s, output: %s)\n' \
    "$cargo_gate_rc" "$cargo_gate_output" >&2
  FAIL=$((FAIL + 1))
fi

rejects_cargo_outcome() {
  local selector="$1" outcome="$2" diagnostic="[FAIL]"
  run_cargo_fixture "$selector" "$outcome"
  # Quiet grep may stop before printf drains a large inventory summary. A
  # here-string prevents that producer's SIGPIPE from failing pipefail after
  # the required diagnostic was already found.
  if [ "$cargo_gate_rc" -ne 0 ] && \
     grep -Fq "$diagnostic" <<< "$cargo_gate_output" && \
     cmp -s "$CARGO_GATE_FIXTURE/expected.argv" "$CARGO_GATE_FIXTURE/argv.log"; then
    printf 'ok - Cargo %s rejects %s and still executes the full inventory\n' "$selector" "$outcome"
    PASS=$((PASS + 1))
  else
    printf 'not ok - Cargo %s/%s (rc=%s, output: %s)\n' \
      "$selector" "$outcome" "$cargo_gate_rc" "$cargo_gate_output" >&2
    FAIL=$((FAIL + 1))
  fi
}
for cargo_gate in "${required_lib_gates[@]}"; do
  rejects_cargo_outcome "--lib|${cargo_gate#*|}" zero '0 passed (vacuous)'
done
rejects_cargo_outcome '--lib|lattice_guard::tests::' zero '0 passed (vacuous)'
rejects_cargo_outcome '--test|a64_lattice_guard_elision_differential' zero '0 passed (vacuous)'
rejects_cargo_outcome '--test|a64_lattice_guard_elision_differential' failed 'test result: FAILED.'
rejects_cargo_outcome '--test|refine_erasure_hazards' zero '0 passed (vacuous)'
rejects_cargo_outcome '--test|refine_erasure_hazards' failed 'test result: FAILED.'
rejects_cargo_outcome '--test|a64_refine_byte_invariance' zero '0 passed (vacuous)'
rejects_cargo_outcome '--test|a64_refine_byte_invariance' failed 'test result: FAILED.'
rejects_cargo_outcome '--test|aarch64_affine_lowering' failed 'test result: FAILED.'
rejects_cargo_outcome '--test|aarch64_trust_ir_affine_lowering' failed 'test result: FAILED.'
rejects_cargo_outcome '--test|aarch64_trust_ir_affine_lowering' zero '0 passed (vacuous)'
# The package integration gates (outside trust-cg-verify) fail closed exactly
# like trust-cg-verify's: a failing, a vacuous/filtered or a timed-out run of
# either WS7.1 target fails the inventory, which still runs to the end.
for cargo_gate in "${required_package_integration_gates[@]}"; do
  rejects_cargo_outcome "--test|${cargo_gate#*|}" failed 'test result: FAILED.'
  rejects_cargo_outcome "--test|${cargo_gate#*|}" zero '0 passed (vacuous)'
  rejects_cargo_outcome "--test|${cargo_gate#*|}" timeout 'TIMEOUT after 17s'
done
rejects_cargo_outcome '--lib|tv2_' empty "NO 'test result' line"
rejects_cargo_outcome '--lib|tv2_' failed 'test result: FAILED.'
rejects_cargo_outcome '--lib|tv2_' failed-rc0 'test result: FAILED.'
rejects_cargo_outcome '--lib|tv2_' missing-count 'test result: ok. no passing count'
rejects_cargo_outcome '--lib|tv2_' not-ok 'test result: not ok.'
rejects_cargo_outcome '--lib|tv2_' contradictory 'test result: ok. 1 passed; 1 failed'
rejects_cargo_outcome '--lib|tv2_' build 'BUILD/COMPILE ERROR'
rejects_cargo_outcome '--lib|tv2_' timeout 'TIMEOUT after 17s'
rejects_cargo_outcome '--lib|tv2_' nonzero-ok '[FAIL]'
run_cargo_fixture '--lib|tv2_' ten
if [ "$cargo_gate_rc" -eq 0 ]; then
  printf 'ok - Cargo library non-vacuity accepts 10 passed\n'
  PASS=$((PASS + 1))
else
  printf 'not ok - Cargo library non-vacuity rejected 10 passed: %s\n' "$cargo_gate_output" >&2
  FAIL=$((FAIL + 1))
fi

for incompatible_mode in --update --pinned --attest --list --list-json --validate-dependency-locks \
  --self-test-clean-cargo-command --run-wasm-oracles; do
  : >"$CARGO_GATE_FIXTURE/argv.log"
  TRUST_CG_DIR="$CARGO_GATE_FIXTURE" \
    "$SOUNDNESS_CHECK" --self-test-cargo-gates "$incompatible_mode" \
    >"$CARGO_GATE_FIXTURE/incompatible.log" 2>&1
  cargo_gate_rc=$?
  if [ "$cargo_gate_rc" -eq 2 ] && [ ! -s "$CARGO_GATE_FIXTURE/argv.log" ]; then
    printf 'ok - Cargo-only self-test refuses %s before dispatch\n' "$incompatible_mode"
    PASS=$((PASS + 1))
  else
    printf 'not ok - Cargo-only self-test combined with %s (rc=%s)\n' \
      "$incompatible_mode" "$cargo_gate_rc" >&2
    FAIL=$((FAIL + 1))
  fi
done

# This mode takes an argument, so test its mutual exclusion separately.
: >"$CARGO_GATE_FIXTURE/argv.log"
TRUST_CG_DIR="$CARGO_GATE_FIXTURE" \
  "$SOUNDNESS_CHECK" --self-test-cargo-gates --validate-clean-summary \
  "$CARGO_GATE_FIXTURE/list.log" >"$CARGO_GATE_FIXTURE/incompatible.log" 2>&1
cargo_gate_rc=$?
if [ "$cargo_gate_rc" -eq 2 ] && [ ! -s "$CARGO_GATE_FIXTURE/argv.log" ]; then
  printf 'ok - Cargo-only self-test refuses Clean-summary mode before dispatch\n'
  PASS=$((PASS + 1))
else
  printf 'not ok - Cargo-only self-test combined with Clean-summary mode (rc=%s)\n' \
    "$cargo_gate_rc" >&2
  FAIL=$((FAIL + 1))
fi

# The main workspace, rustc backend, and fuzz crate resolve dependencies as
# three independent Cargo roots.  A root-only check lets either standalone
# lock silently retain an older TrustIR/Clean/AY universe.  Exercise the
# toolchain-free preflight against a coherent copy, then split one standalone
# lock at a time and require a named refusal.
LOCK_FIXTURE="${TMP}/dependency-locks"
mkdir -p \
  "$LOCK_FIXTURE/crates/rustc-codegen-trust-cg" \
  "$LOCK_FIXTURE/fuzz"
cp "$ROOT/Cargo.toml" "$LOCK_FIXTURE/Cargo.toml"
cp "$ROOT/Cargo.lock" "$LOCK_FIXTURE/Cargo.lock"
cp "$ROOT/crates/rustc-codegen-trust-cg/Cargo.lock" \
  "$LOCK_FIXTURE/crates/rustc-codegen-trust-cg/Cargo.lock"
cp "$ROOT/fuzz/Cargo.lock" "$LOCK_FIXTURE/fuzz/Cargo.lock"

dependency_output=""
if dependency_output="$(
  TRUST_CG_DIR="$LOCK_FIXTURE" \
    "$SOUNDNESS_CHECK" --validate-dependency-locks 2>&1
)" && \
   [ "$(printf '%s\n' "$dependency_output" | grep -Ec '^trust_ir_rev=[0-9a-f]{40}$')" -eq 1 ] && \
   [ "$(printf '%s\n' "$dependency_output" | grep -Ec '^clean_rev=[0-9a-f]{40}$')" -eq 1 ] && \
   [ "$(printf '%s\n' "$dependency_output" | grep -Ec '^ay_rev=[0-9a-f]{40}$')" -eq 1 ]; then
  printf 'ok - independent dependency locks agree on one first-party graph\n'
  PASS=$((PASS + 1))
else
  printf 'not ok - coherent independent dependency locks (output: %s)\n' \
    "${dependency_output:-<empty>}" >&2
  FAIL=$((FAIL + 1))
fi

replace_sha() {
  local file="$1" old="$2" new="$3" tmp="${1}.tmp.$$"
  sed "s/${old}/${new}/g" "$file" >"$tmp" && mv "$tmp" "$file"
}

trust_ir_rev="$(printf '%s\n' "$dependency_output" | sed -n 's/^trust_ir_rev=//p')"
if [ "${#trust_ir_rev}" -eq 40 ]; then
  split_trust_ir_rev="1111111111111111111111111111111111111111"
  replace_sha \
    "$LOCK_FIXTURE/fuzz/Cargo.lock" \
    "$trust_ir_rev" \
    "$split_trust_ir_rev"
  if split_output="$(
    TRUST_CG_DIR="$LOCK_FIXTURE" \
      "$SOUNDNESS_CHECK" --validate-dependency-locks 2>&1
  )"; then
    printf 'not ok - split fuzz TrustIR lock unexpectedly passed: %s\n' "$split_output" >&2
    FAIL=$((FAIL + 1))
  elif printf '%s\n' "$split_output" | grep -Fq 'split first-party trust-ir revisions' && \
       printf '%s\n' "$split_output" | grep -Fq 'fuzz/Cargo.lock'; then
    printf 'ok - split fuzz TrustIR lock fails closed and names the divergent root\n'
    PASS=$((PASS + 1))
  else
    printf 'not ok - split fuzz TrustIR lock diagnostic: %s\n' "$split_output" >&2
    FAIL=$((FAIL + 1))
  fi
  replace_sha \
    "$LOCK_FIXTURE/fuzz/Cargo.lock" \
    "$split_trust_ir_rev" \
    "$trust_ir_rev"
else
  printf 'not ok - coherent dependency output did not yield a TrustIR revision\n' >&2
  FAIL=$((FAIL + 1))
fi

ay_rev="$(printf '%s\n' "$dependency_output" | sed -n 's/^ay_rev=//p')"
if [ "${#ay_rev}" -eq 40 ]; then
  split_ay_rev="2222222222222222222222222222222222222222"
  replace_sha \
    "$LOCK_FIXTURE/crates/rustc-codegen-trust-cg/Cargo.lock" \
    "$ay_rev" \
    "$split_ay_rev"
  if split_output="$(
    TRUST_CG_DIR="$LOCK_FIXTURE" \
      "$SOUNDNESS_CHECK" --validate-dependency-locks 2>&1
  )"; then
    printf 'not ok - split rustc AY lock unexpectedly passed: %s\n' "$split_output" >&2
    FAIL=$((FAIL + 1))
  elif printf '%s\n' "$split_output" | grep -Fq 'split first-party ay revisions' && \
       printf '%s\n' "$split_output" | grep -Fq 'crates/rustc-codegen-trust-cg/Cargo.lock'; then
    printf 'ok - split rustc AY lock fails closed and names the divergent root\n'
    PASS=$((PASS + 1))
  else
    printf 'not ok - split rustc AY lock diagnostic: %s\n' "$split_output" >&2
    FAIL=$((FAIL + 1))
  fi
else
  printf 'not ok - coherent dependency output did not yield an AY revision\n' >&2
  FAIL=$((FAIL + 1))
fi

# Exercise the same high-level Clean build and micro-diversity gate runners the
# constellation uses. Clean builds with the same Trust toolchain as trust-cg
# (owner directive 2026-09-28; the stock "diverse compiler" lane and its
# rustflag neutralization are gone). A fake package targo, named through
# TRUST_TARGO, makes the lane's argv and effective environment observable and
# creates the release binary expected by the build guard: the verb must run in
# targo's explicit unverified lane, in Clean's own target directory, and no
# TRUST_CG_*/TCG_* control may reach targo (trustc refuses to run under one),
# while a test's controls must reach the test through Cargo's runner.
FAKE_PACKAGE="${TMP}/fake-package/bin"
FAKE_CLEAN="${TMP}/fake-clean"
FAKE_HOME="${TMP}/fake-home"
CARGO_AUDIT="${TMP}/clean-cargo.audit"
mkdir -p "$FAKE_PACKAGE" "$FAKE_CLEAN" "$FAKE_HOME"
printf '%s\n' '#!/bin/sh' \
  'case "$*" in -vV) printf "rustc 1.99.0-dev\nbinary: trustc\nhost: aarch64-unknown-linux-gnu\n" ;; *) exit 91 ;; esac' \
  >"$FAKE_PACKAGE/trustc"
cat >"$FAKE_PACKAGE/targo" <<'FAKE_TARGO_SCRIPT'
#!/usr/bin/env bash
set -u
{
  printf 'controls=%s\n' "$(env | grep -E '^(TRUST_CG_|TCG_)' | cut -d= -f1 | sort | tr '\n' ' ')"
  printf 'target_dir=%s\n' "${CARGO_TARGET_DIR-<unset>}"
  printf 'args='
  printf '<%s>' "$@"
  printf '\n'
} >>"$SOUNDNESS_CARGO_AUDIT_LOG"
case "${2-}" in
  build)
    mkdir -p "${CARGO_TARGET_DIR}/release"
    : >"${CARGO_TARGET_DIR}/release/clean"
    chmod +x "${CARGO_TARGET_DIR}/release/clean"
    ;;
  test)
    printf '%s\n' \
      'running 1 test' \
      'test micro_diversity_is_nonvacuous ... ok' \
      'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;'
    ;;
  *) exit 91 ;;
esac
FAKE_TARGO_SCRIPT
chmod +x "$FAKE_PACKAGE/trustc" "$FAKE_PACKAGE/targo"

# The gate exports its own controls too (TRUST_CG_RUN_FORMAL_PROOF_TESTS, and
# TRUST_CG_RUN_ROSETTA_LINKRUN where Rosetta answers), so only the runner's
# head and this fixture's control are pinned.
EXPECTED_TEST_HEAD='args=<--unverified><test><--config><target.aarch64-unknown-linux-gnu.runner=["/usr/bin/env", '
EXPECTED_TEST_TAIL='"TRUST_CG_SELF_TEST_CONTROL=reaches-the-test"]><--locked><-p><clean-kernel><--test><micro_diversity_gate><--><--show-output>'
if output="$(
  env \
    CLEAN_DIR="$FAKE_CLEAN" \
    SOUNDNESS_CARGO_AUDIT_LOG="$CARGO_AUDIT" \
    HOME="$FAKE_HOME" \
    PATH="/usr/bin:/bin" \
    TRUST_TARGO="$FAKE_PACKAGE/targo" \
    TRUST_CG_SELF_TEST_CONTROL=reaches-the-test \
    "$SOUNDNESS_CHECK" --self-test-clean-cargo-command 2>&1
)" && \
   [ "$(grep -c '^controls=$' "$CARGO_AUDIT")" -eq 2 ] && \
   [ "$(grep -c "^target_dir=${FAKE_CLEAN}/target$" "$CARGO_AUDIT")" -eq 2 ] && \
   [ "$(grep -c '^args=<--unverified><build><--locked><--release><-p><clean><--bin><clean><--features><clean/carcara-verify>$' "$CARGO_AUDIT")" -eq 1 ] && \
   [ "$(grep -F "$EXPECTED_TEST_HEAD" "$CARGO_AUDIT" | grep -cF "$EXPECTED_TEST_TAIL")" -eq 1 ]; then
  printf 'ok - Clean builds in the Trust lane and keeps TRUST_CG_* controls out of targo\n'
  PASS=$((PASS + 1))
else
  printf 'not ok - Clean Trust Cargo command (output: %s; audit: %s)\n' \
    "${output:-<empty>}" "$(tr '\n' ' ' <"$CARGO_AUDIT" 2>/dev/null || true)" >&2
  FAIL=$((FAIL + 1))
fi

# A real Trust Cargo fixture proves what the command capture cannot: the
# installed targo accepts Clean's exact per-triple config (whose
# `-Ztrust-verify=off` target stanza is inert in the unverified lane), trustc
# compiles while a TRUST_CG_* control is exported (it refuses to run under one),
# and the control still reaches the test binary through the runner.
REAL_CLEAN="${TMP}/real-clean"
mkdir -p \
  "$REAL_CLEAN/.cargo" \
  "$REAL_CLEAN/clean/src" \
  "$REAL_CLEAN/clean-kernel/src" \
  "$REAL_CLEAN/clean-kernel/tests"
printf '%s\n' \
  '[target.aarch64-apple-darwin]' \
  'rustflags = ["-C", "target-cpu=native", "-Ztrust-verify=off"]' \
  'rustdocflags = ["-Ztrust-verify=off"]' \
  '' \
  '[target.aarch64-unknown-linux-gnu]' \
  'rustflags = ["-C", "target-cpu=native", "-Ztrust-verify=off"]' \
  'rustdocflags = ["-Ztrust-verify=off"]' \
  >"$REAL_CLEAN/.cargo/config.toml"
printf '%s\n' '[toolchain]' 'channel = "trust"' >"$REAL_CLEAN/rust-toolchain.toml"
printf '%s\n' \
  '[workspace]' \
  'resolver = "2"' \
  'members = ["clean", "clean-kernel"]' \
  >"$REAL_CLEAN/Cargo.toml"
printf '%s\n' \
  'version = 4' \
  '' \
  '[[package]]' \
  'name = "clean"' \
  'version = "0.0.0"' \
  '' \
  '[[package]]' \
  'name = "clean-kernel"' \
  'version = "0.0.0"' \
  >"$REAL_CLEAN/Cargo.lock"
printf '%s\n' \
  '[package]' \
  'name = "clean"' \
  'version = "0.0.0"' \
  'edition = "2021"' \
  '[features]' \
  'carcara-verify = []' \
  >"$REAL_CLEAN/clean/Cargo.toml"
printf '%s\n' \
  '#[cfg(not(feature = "carcara-verify"))]' \
  'compile_error!("soundness builds must preserve the packaged checker capability");' \
  'fn main() {}' >"$REAL_CLEAN/clean/src/main.rs"
printf '%s\n' \
  '[package]' \
  'name = "clean-kernel"' \
  'version = "0.0.0"' \
  'edition = "2021"' \
  >"$REAL_CLEAN/clean-kernel/Cargo.toml"
printf '%s\n' 'pub fn diversity_witness() -> bool { true }' \
  >"$REAL_CLEAN/clean-kernel/src/lib.rs"
printf '%s\n' \
  '#[test]' \
  'fn micro_diversity_is_nonvacuous() {' \
  '    assert!(clean_kernel::diversity_witness());' \
  '    assert_eq!(' \
  '        std::env::var("TRUST_CG_SELF_TEST_CONTROL").as_deref(),' \
  '        Ok("reaches-the-test")' \
  '    );' \
  '}' \
  >"$REAL_CLEAN/clean-kernel/tests/micro_diversity_gate.rs"

if output="$(
  CLEAN_DIR="$REAL_CLEAN" \
  TRUST_CG_SELF_TEST_CONTROL=reaches-the-test \
    "$SOUNDNESS_CHECK" --self-test-clean-cargo-command 2>&1
)" && [ -x "$REAL_CLEAN/target/release/clean" ]; then
  printf 'ok - the installed Trust toolchain builds Clean'"'"'s config and runs its gate\n'
  PASS=$((PASS + 1))
else
  printf 'not ok - real Trust Cargo Clean lane (output: %s)\n' \
    "${output:-<empty>}" >&2
  FAIL=$((FAIL + 1))
fi

printf '%d passed, %d failed\n' "$PASS" "$FAIL"
[ "$FAIL" -eq 0 ]
