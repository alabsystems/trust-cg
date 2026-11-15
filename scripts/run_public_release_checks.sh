#!/bin/sh
#
# Exact anonymous-clone validation for the publication candidate.
#
# Usage: scripts/run_public_release_checks.sh [--dry-run] [--evidence-dir DIR]
#
# TRUST_CG_PROOF_GATE selects the solver policy with the spelling
# scripts/run_full_test_matrix.sh reads. It is consumed here and never exported
# to targo, whose tests refuse unknown TRUST_CG_* controls.
#   auto     Default, and what publish/config.sh runs. A lane that cannot run on
#            this host or without an AY solver is recorded as an exclusion and
#            announced as NON-QUALIFYING; the gate still exits 0 when every
#            executed lane passes.
#   require  Solver-required, zero-exclusion mode. AY and Clean must resolve
#            through a pinned route (AY: an absolute AY_SOLVER_PATH or the
#            build toolchain's bin/ay; Clean: explicit override or aterm's
#            managed store) and their identities are recorded; any planned exclusion
#            refuses the run before a lane starts; scripts/check_proof_gate.sh
#            runs. Exit 0 means the recorded verdict is qualifying.
# Hosts: aarch64-apple-darwin keeps its lanes, runs
# scripts/check_darwin_aarch64.py only when that runner exists and always runs
# scripts/check_darwin_aarch64_bridge.py (decision OD-04);
# aarch64-unknown-linux-gnu also runs scripts/check_linux_aarch64.py,
# scripts/check_linux_aarch64_bridge.py and the AOT arithmetic matrix
# (scripts/check_aarch64_aot_arithmetic.py against a CLI the lane builds;
# OD-12, OD-13), retaining their reports in the evidence directory. Both native
# floors run with --require-offline-deps (OD-09), and every AArch64 host runs
# scripts/check_companion_coherence.py (OD-08); the rulings are in
# docs/decision-record.md. x86_64-apple-darwin and x86_64-unknown-linux-gnu retain
# an accounting-only plan of unqualified native floor/bridge (Linux names its
# diagnostic runners) and AArch64-only PGO/JIT lanes; they never run Cargo or
# qualify a release. Every supported
# host writes <evidence-dir>/summary.json through
# scripts/release_gate_summary.py; its non_qualifying_reasons list is the
# machine-readable verdict. The evidence directory defaults to a new temporary
# directory and must lie outside the source tree. --dry-run records the mode,
# host and lane plan without running a lane; AArch64 plans also resolve solver
# identities, while x86 accounting-only plans do not probe them.
#
# Every Cargo lane runs on the installed Trust package (rust-toolchain.toml
# `channel = "trust"`; owner directive 2026-09-28) that scripts/trust_toolchain.py
# resolves: `targo metadata`, and `targo --unverified <verb>` through
# scripts/trust_cargo.sh. There is no stock toolchain and no stock fallback.

set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO_ROOT=$(CDPATH= cd -- "${SCRIPT_DIR}/.." && pwd)
SUMMARY_TOOL="${SCRIPT_DIR}/release_gate_summary.py"
CODEGEN_RUNNER="${SCRIPT_DIR}/run_public_release_codegen_tests.sh"
BRIDGE_TOOLCHAIN_FILE=crates/rustc-codegen-trust-cg/rust-toolchain.toml

usage() {
    awk 'NR >= 3 && /^#/ { sub(/^# ?/, ""); print; next } NR >= 3 { exit }' "$0"
}

ORIGINAL_ARGS="$*"
DRY_RUN=0
EVIDENCE_DIR=
while [ $# -gt 0 ]; do
    case "$1" in
        --dry-run)
            DRY_RUN=1
            ;;
        --evidence-dir)
            if [ $# -lt 2 ] || [ -z "$2" ]; then
                echo "run_public_release_checks: --evidence-dir requires a path" >&2
                exit 2
            fi
            EVIDENCE_DIR=$2
            shift
            ;;
        --evidence-dir=?*)
            EVIDENCE_DIR=${1#--evidence-dir=}
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            echo "run_public_release_checks: unknown argument: $1" >&2
            usage >&2
            exit 2
            ;;
    esac
    shift
done

GATE_MODE=${TRUST_CG_PROOF_GATE:-auto}
case "${GATE_MODE}" in
    auto|require) ;;
    *)
        echo "run_public_release_checks: TRUST_CG_PROOF_GATE must be auto or require, got '${GATE_MODE}'" >&2
        exit 2
        ;;
esac
unset TRUST_CG_PROOF_GATE

# A relative evidence directory is relative to the caller, not the source root.
if [ -n "${EVIDENCE_DIR}" ]; then
    case "${EVIDENCE_DIR}" in
        /*) ;;
        *) EVIDENCE_DIR="$(pwd)/${EVIDENCE_DIR}" ;;
    esac
fi
cd "${REPO_ROOT}"

# Release validation includes generated, memory-intensive integration targets.
# Run libtest serially by default while preserving an explicit caller override.
: "${RUST_TEST_THREADS:=1}"
export RUST_TEST_THREADS

# The one installed Trust package every lane runs on. The AArch64 hosts assert
# its exact compiler identity: the generated kernel differentials compare JIT
# code with host Rust values whose repr(Rust) layout is compiler-specific, and
# crates/trust-cg-codegen/fixture_toolchain.rs certifies exactly the compilers
# scripts/release_trust_compilers.txt lists for each host. A Trust update
# therefore moves that list, the certification and its qualification run
# together. There is no x86_64 Trust package (no authenticated x86_64 sysroot,
# X12), so those hosts keep the accounting-only profile below and are
# identified without a compiler.
RELEASE_TRUST_COMPILERS="${SCRIPT_DIR}/release_trust_compilers.txt"
# The `trustc --version` lines the list certifies for host $1, one per line.
certified_trust_compilers() {
    awk -F '\t' -v host="$1" '$0 !~ /^#/ && NF == 2 && $1 == host { print $2 }' \
        "${RELEASE_TRUST_COMPILERS}"
}
# Whether $2 is, whole and exactly, one of the compilers certified for host $1.
is_certified_trust_compiler() {
    certified_trust_compilers "$1" | {
        while IFS= read -r certified; do
            [ "${certified}" = "$2" ] && exit 0
        done
        exit 1
    }
}
if TRUST_RECORD=$(python3 -B scripts/trust_toolchain.py --print json 2>/dev/null); then
    trust_field() {
        printf '%s' "${TRUST_RECORD}" | python3 -c 'import json, sys; print(json.load(sys.stdin)[sys.argv[1]])' "$1"
    }
    actual_host=$(trust_field host)
    TRUST_TARGO=$(trust_field targo)
    TRUST_COMPILER=$(trust_field compiler)
    export TRUST_TARGO
else
    case "$(uname -s)-$(uname -m)" in
        Darwin-x86_64) actual_host=x86_64-apple-darwin ;;
        Linux-x86_64) actual_host=x86_64-unknown-linux-gnu ;;
        *)
            echo "run_public_release_checks: no installed Trust package resolves (scripts/trust_toolchain.py):" >&2
            python3 -B scripts/trust_toolchain.py --print summary >&2 || true
            echo "  every Cargo lane runs on the Trust toolchain; there is no stock fallback" >&2
            exit 1
            ;;
    esac
    TRUST_TARGO=
    TRUST_COMPILER=
fi
case "${actual_host}" in
    aarch64-apple-darwin|aarch64-unknown-linux-gnu)
        # The host's soundness pin: scripts/soundness_attestation.py reads
        # this exact spelling (TRUSTC_PIN) as the one compiler the soundness
        # legs must run on. The release gate accepts every compiler the list
        # certifies for the host, and the pin is one of them
        # (scripts/tests/test_release_harness_syntax_gate.py).
        case "${actual_host}" in
            aarch64-apple-darwin)
                expected_trustc='rustc 1.101.0-dev (29ebb403d 2026-10-28) (trustc 0.12.0+g29ebb403d)'
                ;;
            aarch64-unknown-linux-gnu)
                expected_trustc='rustc 1.99.0-dev (ae9c2c1da 2026-09-21) (trustc 0.1.0)'
                ;;
        esac
        certified_trustc=$(certified_trust_compilers "${actual_host}") || certified_trustc=
        if [ -z "${certified_trustc}" ]; then
            echo "run_public_release_checks: ${RELEASE_TRUST_COMPILERS} certifies no Trust compiler for ${actual_host}" >&2
            exit 1
        fi
        actual_trustc=$("${TRUST_COMPILER}" --version)
        actual_targo=$("${TRUST_TARGO}" --unverified --version) || {
            echo "run_public_release_checks: ${TRUST_TARGO} rejects --unverified: it is not targo" >&2
            exit 1
        }
        if ! is_certified_trust_compiler "${actual_host}" "${actual_trustc}"; then
            echo "run_public_release_checks: expected one of the ${actual_host} compilers in ${RELEASE_TRUST_COMPILERS}" \
                "($(printf '%s\n' "${certified_trustc}" | paste -s -d ';' -); soundness pin ${expected_trustc})," \
                "got ${actual_trustc}" >&2
            exit 1
        fi
        # targo must come from the same build: `targo <release> (<commit> <date>) (targo ...)`.
        trustc_build=$(printf '%s\n' "${actual_trustc}" | sed -n 's/^rustc \([^ ]* ([^)]*)\) (trustc .*/\1/p')
        case "${actual_targo}" in
            "targo ${trustc_build} (targo "*) ;;
            *)
                echo "run_public_release_checks: targo ${actual_targo} is not the build of ${actual_trustc}" >&2
                exit 1
                ;;
        esac
        ;;
    x86_64-apple-darwin|x86_64-unknown-linux-gnu) ;;
    *)
        echo "run_public_release_checks: unsupported host ${actual_host:-unknown}" >&2
        exit 1
        ;;
esac
TRUST_CARGO="${SCRIPT_DIR}/trust_cargo.sh"

# Retained evidence lives outside the source tree: the Linux runners fingerprint
# the checkout and reject output inside it. An existing summary is prior
# evidence and is never overwritten.
repo_physical=$(pwd -P)
if [ -z "${EVIDENCE_DIR}" ]; then
    EVIDENCE_DIR=$(mktemp -d "${TMPDIR:-/tmp}/trust-cg-public-release.XXXXXX")
else
    case "${EVIDENCE_DIR}/" in
        "${REPO_ROOT}/"*|"${repo_physical}/"*)
            echo "run_public_release_checks: --evidence-dir must lie outside the source tree: ${EVIDENCE_DIR}" >&2
            exit 2
            ;;
    esac
    mkdir -p -- "${EVIDENCE_DIR}"
fi
EVIDENCE_DIR=$(CDPATH= cd -- "${EVIDENCE_DIR}" && pwd -P)
case "${EVIDENCE_DIR}/" in
    "${repo_physical}/"*)
        echo "run_public_release_checks: --evidence-dir must lie outside the source tree: ${EVIDENCE_DIR}" >&2
        exit 2
        ;;
esac
SUMMARY="${EVIDENCE_DIR}/summary.json"
summary() {
    python3 -B "${SUMMARY_TOOL}" "$@" --path "${SUMMARY}"
}
summary init --gate run_public_release_checks --mode "${GATE_MODE}" \
    --host "${actual_host}" --evidence-dir "${EVIDENCE_DIR}" \
    --command "$0 ${ORIGINAL_ARGS}"

GATE_COMPLETED=0
CURRENT_LANE=
on_exit() {
    status=$?
    trap - EXIT
    if [ "${GATE_COMPLETED}" -eq 1 ]; then
        exit "${status}"
    fi
    if [ -n "${CURRENT_LANE}" ]; then
        summary lane --name "${CURRENT_LANE}" --status fail --detail "exit status ${status}" || true
    fi
    if [ "${status}" -eq 0 ]; then
        status=1
    fi
    summary finish --status fail >/dev/null || true
    echo "run_public_release_checks: FAIL (summary ${SUMMARY})" >&2
    exit "${status}"
}
trap on_exit EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

# The x86 release profile is accounting only. Linux x86-64 has standalone
# diagnostic runners (scripts/check_linux_x86_64.py and
# scripts/check_linux_x86_64_bridge.py), but by their own contract and
# docs/linux-x86-64-completion.md neither is release qualification, so this
# gate records them and does not run them; x86-64 macOS has no native runner.
# The current PGO/JIT lanes are AArch64 evidence. Do not invoke the AArch64
# codegen runner or any Cargo lane here.
record_x86_plan() {
    case "${actual_host}" in
        x86_64-apple-darwin)
            native_prefix=darwin-x86_64
            floor_detail="no native ${actual_host} floor runner"
            bridge_detail="no native ${actual_host} rustc-bridge runner"
            ;;
        x86_64-unknown-linux-gnu)
            native_prefix=linux-x86_64
            floor_detail="scripts/check_linux_x86_64.py is a diagnostic floor, not release qualification, and is not run here"
            bridge_detail="scripts/check_linux_x86_64_bridge.py is a bridge diagnostic, not release qualification, and is not run here"
            ;;
    esac
    summary lane --name "${native_prefix}-floor" --status unavailable \
        --detail "${floor_detail}; no Cargo lanes were executed"
    summary lane --name "${native_prefix}-bridge" --status unavailable \
        --detail "${bridge_detail}; bridge evidence is missing"
    summary lane --name pgo-runtime --status excluded \
        --detail "scripts/test_pgo_runtime.sh is AArch64-only; no x86 AOT PGO evidence"
    summary exclusion --lane pgo-runtime --kind host --value scripts/test_pgo_runtime.sh \
        --reason "the AArch64 AOT PGO runtime lane is not x86 evidence on ${actual_host}"
    summary lane --name codegen-capstones --status excluded \
        --detail "the 52 in-process JIT capstones are AArch64-only; no x86 JIT evidence"
    summary exclusion --lane codegen-capstones --kind host --value "52 exact policy tests" \
        --reason "AArch64 JIT capstones are not qualified on ${actual_host}"
}

case "${actual_host}" in
    x86_64-apple-darwin|x86_64-unknown-linux-gnu)
        record_x86_plan
        x86_blockers=$(summary blockers)
        printf '%s\n' "${x86_blockers}" | while IFS= read -r blocker; do
            echo "!!! run_public_release_checks: NON-QUALIFYING: ${blocker} !!!" >&2
        done
        if [ "${GATE_MODE}" = require ]; then
            summary finish --status fail >/dev/null
            GATE_COMPLETED=1
            echo "run_public_release_checks: TRUST_CG_PROOF_GATE=require refuses the x86 accounting-only profile; nothing was run (summary ${SUMMARY})" >&2
            exit 1
        fi
        if [ "${DRY_RUN}" -eq 1 ]; then
            summary finish --status dry-run >/dev/null
            GATE_COMPLETED=1
            echo "Public-release anonymous-clone checks: DRY RUN (NON-QUALIFYING; plan recorded in ${SUMMARY})"
            exit 0
        fi
        summary finish --status fail >/dev/null
        GATE_COMPLETED=1
        echo "run_public_release_checks: x86 release lanes are unavailable; no Cargo lane was run (summary ${SUMMARY})" >&2
        exit 1
        ;;
esac

# `AY_SOLVER_PATH` is the canonical override and the ONLY name the backend
# reads (crates/trust-cg-verify/src/ay_identity.rs: it must be absolute and is
# identity-checked exactly like the toolchain's own `bin/ay`; there is no PATH
# lookup and no other automatic route). `TCG_SOLVER_PATH` is accepted as a
# legacy alias and exported to the canonical name, so the tests see exactly the
# solver this gate saw. scripts/release_gate_summary.py mirrors that rule.
if [ -z "${AY_SOLVER_PATH:-}" ] && [ -n "${TCG_SOLVER_PATH:-}" ]; then
    export AY_SOLVER_PATH="${TCG_SOLVER_PATH}"
fi
# trustc refuses to run while any TCG_* variable is set; the alias has been
# consumed into the canonical name the tests read.
unset TCG_SOLVER_PATH
# Sets RESOLVED_PATH/RESOLVED_ROUTE/RESOLVED_PINNING and RESOLVE_STATUS
# (0 found, 3 absent, 4 invalid explicit override) for `ay` or `clean`.
resolve_proof_tool() {
    RESOLVED_PATH=
    RESOLVED_ROUTE=
    RESOLVED_PINNING=
    set +e
    resolved=$(python3 -B "${SUMMARY_TOOL}" resolve --tool "$1" --host "${actual_host}")
    RESOLVE_STATUS=$?
    set -e
    case "${RESOLVE_STATUS}" in
        0)
            RESOLVED_PATH=$(printf '%s\n' "${resolved}" | cut -f1)
            RESOLVED_ROUTE=$(printf '%s\n' "${resolved}" | cut -f2)
            RESOLVED_PINNING=$(printf '%s\n' "${resolved}" | cut -f3)
            ;;
        3|4) ;;
        *)
            echo "run_public_release_checks: proof-tool resolution failed (exit ${RESOLVE_STATUS})" >&2
            exit 1
            ;;
    esac
}
resolve_proof_tool ay
AY_PATH=${RESOLVED_PATH}
AY_ROUTE=${RESOLVED_ROUTE}
AY_PINNING=${RESOLVED_PINNING}
AY_STATUS=${RESOLVE_STATUS}
resolve_proof_tool clean
CLEAN_PATH=${RESOLVED_PATH}
CLEAN_ROUTE=${RESOLVED_ROUTE}
CLEAN_PINNING=${RESOLVED_PINNING}
CLEAN_STATUS=${RESOLVE_STATUS}
if [ "${GATE_MODE}" = require ]; then
    if [ "${AY_PINNING}" != pinned ] || [ "${CLEAN_PINNING}" != pinned ]; then
        echo "run_public_release_checks: TRUST_CG_PROOF_GATE=require needs AY and Clean through a pinned route" >&2
        echo "  (AY: ${AY_PATH:-unresolved} ${AY_ROUTE:-status ${AY_STATUS}}; Clean: ${CLEAN_PATH:-unresolved} ${CLEAN_ROUTE:-status ${CLEAN_STATUS}})." >&2
        echo "  Refusing to run instead of reporting a release verified modulo the solver lanes." >&2
        echo "  Set AY_SOLVER_PATH and TCG_EXTERNAL_CLEAN_CHECKER to absolute executables or build with a Trust toolchain that ships its AY and install aterm's managed clean." >&2
        exit 1
    fi
fi
AY_AVAILABLE=0
if [ -n "${AY_PATH}" ]; then
    AY_AVAILABLE=1
fi
if [ -n "${AY_PATH}" ] || [ -n "${CLEAN_PATH}" ]; then
    set --
    if [ -n "${AY_PATH}" ]; then
        set -- "$@" --ay "${AY_PATH}" --ay-route "${AY_ROUTE}"
    fi
    if [ -n "${CLEAN_PATH}" ]; then
        set -- "$@" --clean "${CLEAN_PATH}" --clean-route "${CLEAN_ROUTE}"
    fi
    summary solver "$@"
fi

# The standalone rustc backend builds with its own pinned toolchain. The release
# contract is the exact committed pin, so a bridge toolchain migration must
# update EXPECTED_BRIDGE_CHANNEL, this gate's driver and its tests together. The
# cache directory is the one scripts/run_full_test_matrix.sh
# --check-rustc-backend-env builds, so the test lane exercises that exact dylib.
EXPECTED_BRIDGE_CHANNEL=trust
BRIDGE_CHANNEL=$(sed -n 's/^channel = "\([^"]*\)"$/\1/p' "${BRIDGE_TOOLCHAIN_FILE}" 2>/dev/null || true)
BRIDGE_TARGET_DIR="${REPO_ROOT}/target/rustc-codegen-trust-cg-${EXPECTED_BRIDGE_CHANNEL}"
bridge_toolchain_pin() {
    if [ "$(grep -c '^channel = ' "${BRIDGE_TOOLCHAIN_FILE}")" -ne 1 ]; then
        echo "run_public_release_checks: ${BRIDGE_TOOLCHAIN_FILE} must contain exactly one channel" >&2
        return 1
    fi
    if [ "${BRIDGE_CHANNEL}" != "${EXPECTED_BRIDGE_CHANNEL}" ]; then
        echo "run_public_release_checks: ${BRIDGE_TOOLCHAIN_FILE} must pin exactly channel = \"${EXPECTED_BRIDGE_CHANNEL}\", got '${BRIDGE_CHANNEL}'" >&2
        return 1
    fi
}
bridge_release_tests() {
    # Same package as the availability probe, resolved by
    # scripts/trust_toolchain.py: the PATH trustc/targo pair from one installed
    # package with its branded 40-hex commit identity and sysroot. The retired
    # stock nightly lane is refused, never selected. targo's
    # unverified lane is diagnostic and makes no Trust-verification claim.
    trust_compiler=$(python3 -B scripts/trust_toolchain.py --print compiler) || return 1
    trust_targo=$(python3 -B scripts/trust_toolchain.py --print targo) || return 1
    python3 -B scripts/trust_toolchain.py --print summary || return 1
    set -- env "RUSTC=${trust_compiler}" "CARGO_TARGET_DIR=${BRIDGE_TARGET_DIR}" "${trust_targo}" --unverified
    (
        cd crates/rustc-codegen-trust-cg
        "$@" test --release --locked --all-features --all-targets --no-fail-fast -- \
            --test-threads="${RUST_TEST_THREADS}"
        # No doctest lane: the backend is crate-type ["dylib"] only (the
        # rustc_codegen_cranelift convention), and targo hard-errors on
        # `targo --unverified test --doc` for a package with no doctestable lib target
        # ("no library targets found"). The --all-targets run above is the
        # complete test surface for this crate.
    )
}
# The bridge build-probe contract tests require explicit absolute Trust tools
# (no PATH fallback). The gate supplies the same package its bridge lanes use;
# an unresolvable package fails this lane rather than skipping those tests.
# test_cargo_config_audit (installed Targo model) and test_matrix_capture (the
# JSON libtest protocol) use the same pair instead of PATH.
python_unit_tests() {
    # tomllib is Python 3.11+: scripts/cargo_config_audit.py fails closed
    # without it and test_bump_trust_ir_pin cannot import. macOS /usr/bin/python3
    # is 3.9, so name the interpreter instead of reporting dozens of red tests.
    if ! python3 -c 'import sys; sys.exit(sys.version_info < (3, 11))'; then
        echo "run_public_release_checks: python-unit-tests needs python3 >= 3.11 (tomllib); $(command -v python3) is $(python3 --version 2>&1)" >&2
        return 1
    fi
    BRIDGE_PROBE_TARGO="${TRUST_TARGO}" BRIDGE_PROBE_TRUSTC="${TRUST_COMPILER}" \
        python3 -B -m unittest discover -s scripts/tests -p 'test_*.py'
}
vendor_licenses_present() {
    test -s third_party/vendor/xxhash-LICENSE
    test -s third_party/vendor/rust-stdlib-SipHasher13-LICENSE
}
aot_arithmetic_matrix() {
    "${TRUST_CARGO}" build --release --locked -p trust-cg-cli --bin trust-cg
    python3 -B scripts/check_aarch64_aot_arithmetic.py --trust-cg target/release/trust-cg \
        --require-clean --out "${EVIDENCE_DIR}/aarch64-aot-arithmetic"
}
cargo_metadata_locked() {
    "${TRUST_TARGO}" metadata --locked --format-version 1 >/dev/null
    "${TRUST_TARGO}" metadata --locked \
        --manifest-path crates/rustc-codegen-trust-cg/Cargo.toml \
        --format-version 1 >/dev/null
    "${TRUST_TARGO}" metadata --locked --manifest-path fuzz/Cargo.toml \
        --format-version 1 >/dev/null
}

# The lane list is evaluated twice: PHASE=plan records every lane, exclusion
# and partition without running anything, so require mode can refuse before a
# lane starts; PHASE=run executes the same list. Lanes are invoked outside any
# conditional so a failing step stops the gate under set -e, and the EXIT trap
# records which lane failed.
PHASE=plan
LANE_OUTPUT=
LANE_DETAIL=
lane() {
    lane_name=$1
    shift
    if [ "${PHASE}" = plan ]; then
        lane_detail=${LANE_DETAIL:-$*}
        if [ -n "${LANE_OUTPUT}" ]; then
            summary lane --name "${lane_name}" --status planned --detail "${lane_detail}" --output "${LANE_OUTPUT}"
        else
            summary lane --name "${lane_name}" --status planned --detail "${lane_detail}"
        fi
        return 0
    fi
    CURRENT_LANE=${lane_name}
    lane_log="${EVIDENCE_DIR}/lanes/${lane_name}.log"
    lane_status_file="${EVIDENCE_DIR}/lanes/${lane_name}.status"
    mkdir -p -- "${EVIDENCE_DIR}/lanes"
    rm -f -- "${lane_status_file}"
    summary lane --name "${lane_name}" --status running --log "${lane_log}"
    echo ">>> public-release lane: ${lane_name} (log ${lane_log})"
    # The lane runs in a subshell that inherits set -e outside any AND-OR list,
    # so a failing step inside a function lane still stops it. Its EXIT trap
    # records the status that the tee pipeline would otherwise hide; a missing
    # status file (the subshell was killed) is a failure.
    ( trap 'echo "$?" > "${lane_status_file}"' EXIT; "$@" ) 2>&1 | tee "${lane_log}"
    lane_status=$(cat "${lane_status_file}" 2>/dev/null || echo missing)
    rm -f -- "${lane_status_file}"
    if [ "${lane_status}" != 0 ]; then
        echo "run_public_release_checks: lane ${lane_name} failed (status ${lane_status}; log ${lane_log})" >&2
        case "${lane_status}" in
            ''|*[!0-9]*) lane_status=1 ;;
        esac
        exit "${lane_status}"
    fi
    summary lane --name "${lane_name}" --status pass
    CURRENT_LANE=
}
lane_with_output() {
    LANE_OUTPUT=$2
    output_lane=$1
    shift 2
    lane "${output_lane}" "$@"
    LANE_OUTPUT=
}
# A lane whose command is a shell function records what that function runs.
described_lane() {
    LANE_DETAIL=$2
    described=$1
    shift 2
    lane "${described}" "$@"
    LANE_DETAIL=
}
record_exclusion() {
    if [ "${PHASE}" = plan ]; then
        summary exclusion --lane "$1" --kind "$2" --value "$3" --reason "$4"
    fi
}
record_lane_state() {
    if [ "${PHASE}" = plan ]; then
        summary lane --name "$1" --status "$2" --detail "$3"
    fi
}

gate_lanes() {
    lane authority-preflight python3 -B scripts/check_trust_default_authority.py --root .
    # Every companion pin in the tree must agree with Cargo.lock (OD-08).
    lane companion-coherence python3 -B scripts/check_companion_coherence.py
    described_lane python-unit-tests \
        "python3 -B -m unittest discover -s scripts/tests -p 'test_*.py' with BRIDGE_PROBE_TARGO/TRUSTC from scripts/trust_toolchain.py" \
        python_unit_tests

    # The authoritative 18-program correctness harness is release machinery,
    # even though a normal smoke does not run its timing lanes. Parse it here
    # so a syntax regression cannot make the advertised differential gate
    # silently unusable.
    lane harness-syntax python3 -c 'import ast, pathlib, sys; ast.parse(pathlib.Path(sys.argv[1]).read_text(), filename=sys.argv[1])' \
        benchmarks/beat-llvm/run.py
    # run.py imports its RSS sampler and CPU-provenance probes; a syntax error
    # in either breaks the harness exactly as one in run.py would.
    lane harness-helper-syntax python3 -c 'import ast, pathlib, sys; [ast.parse(pathlib.Path(p).read_text(), filename=p) for p in sys.argv[1:]]' \
        benchmarks/beat-llvm/peak_rss.py benchmarks/beat-llvm/hostinfo.py

    lane timeout-runner-tests scripts/test_run_with_timeout.sh
    lane soundness-harness-tests scripts/test_soundness_check.sh
    lane sat-fixtures python3 crates/trust-cg-sat-host/tests/fixtures/sat_corpus/generators.py --check
    described_lane vendor-licenses \
        "test -s third_party/vendor/xxhash-LICENSE third_party/vendor/rust-stdlib-SipHasher13-LICENSE" \
        vendor_licenses_present

    described_lane cargo-metadata \
        "targo metadata --locked for the root, crates/rustc-codegen-trust-cg and fuzz manifests" \
        cargo_metadata_locked
    lane cargo-check-workspace "${TRUST_CARGO}" check --locked --workspace --all-targets --all-features
    lane cargo-check-fuzz "${TRUST_CARGO}" check --locked --manifest-path fuzz/Cargo.toml

    if [ "${actual_host}" = aarch64-apple-darwin ]; then
        lane pgo-runtime scripts/test_pgo_runtime.sh
    else
        record_lane_state pgo-runtime excluded \
            "scripts/test_pgo_runtime.sh executes a real PGO run only on aarch64-apple-darwin"
        record_exclusion pgo-runtime host scripts/test_pgo_runtime.sh \
            "the AOT PGO runtime lane is not ported to ${actual_host}"
    fi

    # Strict formal floor: the Rust gate admits the identity-checked toolchain
    # AY (crates/trust-cg-verify/src/ay_identity.rs) and that toolchain's Clean
    # (else the managed one), and fails closed on an incapable solver, a
    # counterexample or any statistical fallback. Auto mode leaves it to scripts/run_full_test_matrix.sh.
    if [ "${GATE_MODE}" = require ]; then
        lane proof-gate scripts/check_proof_gate.sh
    fi

    # trust-cg-codegen leaves the workspace lane so its state-sensitive
    # generated capstones never share a libtest process; the partition records
    # that the codegen lane below must pass for the package to count as covered.
    # trust-cg-verify's CEGIS lane shells out to an `ay` BINARY; without one its
    # solver-backed tests fail on the environment rather than the code, so auto
    # mode excludes the package and records that exclusion.
    if [ "${PHASE}" = plan ]; then
        summary partition --package trust-cg-codegen --from-lane workspace --covered-by codegen
    fi
    if [ "${AY_AVAILABLE}" -eq 1 ]; then
        lane workspace "${TRUST_CARGO}" test --locked --workspace --all-features \
            --exclude trust-cg-codegen --no-fail-fast -- \
            --test-threads="${RUST_TEST_THREADS}"
    else
        if [ "${AY_STATUS}" -eq 4 ]; then
            record_exclusion workspace cargo-exclude trust-cg-verify \
                "the explicit AY_SOLVER_PATH override is not an absolute path to an executable"
        else
            record_exclusion workspace cargo-exclude trust-cg-verify \
                "no AY solver resolvable: the build toolchain's sysroot ships no bin/ay; build with a Trust toolchain that ships its AY, or set an absolute AY_SOLVER_PATH (TCG_SOLVER_PATH alias) to a copy of that exact AY"
        fi
        lane workspace "${TRUST_CARGO}" test --locked --workspace --all-features \
            --exclude trust-cg-codegen --exclude trust-cg-verify --no-fail-fast -- \
            --test-threads="${RUST_TEST_THREADS}"
    fi
    if [ "${PHASE}" = plan ]; then
        "${CODEGEN_RUNNER}" --plan --proof-gate="${GATE_MODE}" --summary="${SUMMARY}"
    fi
    lane codegen "${CODEGEN_RUNNER}" --release --proof-gate="${GATE_MODE}" --summary="${SUMMARY}"

    described_lane bridge-toolchain-pin \
        "${BRIDGE_TOOLCHAIN_FILE} pins exactly channel = \"${EXPECTED_BRIDGE_CHANNEL}\" (found '${BRIDGE_CHANNEL}')" \
        bridge_toolchain_pin
    lane bridge-env scripts/run_full_test_matrix.sh --check-rustc-backend-env
    described_lane bridge-tests \
        "(cd crates/rustc-codegen-trust-cg && env RUSTC=${TRUST_COMPILER} CARGO_TARGET_DIR=${BRIDGE_TARGET_DIR} ${TRUST_TARGO} --unverified test --release --locked --all-features --all-targets --no-fail-fast)" \
        bridge_release_tests

    # The native floors judge the pinned companion revisions and never fetch
    # (OD-09): the metadata and check lanes above fetched the locked ones.
    case "${actual_host}" in
        aarch64-unknown-linux-gnu)
            lane_with_output linux-aarch64-floor "${EVIDENCE_DIR}/linux-aarch64-floor" \
                python3 -B scripts/check_linux_aarch64.py --require-offline-deps \
                    --out "${EVIDENCE_DIR}/linux-aarch64-floor"
            lane_with_output linux-aarch64-bridge "${EVIDENCE_DIR}/linux-aarch64-bridge" \
                python3 -B scripts/check_linux_aarch64_bridge.py \
                    --out "${EVIDENCE_DIR}/linux-aarch64-bridge" --target-dir "${BRIDGE_TARGET_DIR}"
            # The 48-case AOT arithmetic matrix is required here (OD-12) and
            # judges a CLI this lane builds from the checked-out tree (OD-13).
            # It replays through AY and Clean, so without both it is an
            # exclusion, which require mode refuses before any lane starts.
            if [ "${AY_AVAILABLE}" -eq 1 ] && [ -n "${CLEAN_PATH}" ]; then
                LANE_OUTPUT="${EVIDENCE_DIR}/aarch64-aot-arithmetic"
                described_lane aarch64-aot-arithmetic \
                    "${TRUST_CARGO} build --release --locked -p trust-cg-cli --bin trust-cg, then python3 -B scripts/check_aarch64_aot_arithmetic.py --trust-cg target/release/trust-cg --require-clean --out ${EVIDENCE_DIR}/aarch64-aot-arithmetic" \
                    aot_arithmetic_matrix
                LANE_OUTPUT=
            else
                record_lane_state aarch64-aot-arithmetic excluded \
                    "scripts/check_aarch64_aot_arithmetic.py replays every exported query through AY and Clean"
                record_exclusion aarch64-aot-arithmetic solver scripts/check_aarch64_aot_arithmetic.py \
                    "the matrix needs both AY and Clean through a pinned route (AY: ${AY_PATH:-unresolved}; Clean: ${CLEAN_PATH:-unresolved})"
            fi
            ;;
        aarch64-apple-darwin)
            if [ -f scripts/check_darwin_aarch64.py ]; then
                lane_with_output darwin-aarch64-floor "${EVIDENCE_DIR}/darwin-aarch64-floor" \
                    python3 -B scripts/check_darwin_aarch64.py --require-offline-deps \
                        --out "${EVIDENCE_DIR}/darwin-aarch64-floor"
            else
                record_lane_state darwin-aarch64-floor unavailable \
                    "scripts/check_darwin_aarch64.py is not present; no Darwin native floor runner exists in this checkout"
            fi
            # The required Darwin bridge runner (OD-04): red until the bridge
            # fixtures run green on this host.
            lane_with_output darwin-aarch64-bridge "${EVIDENCE_DIR}/darwin-aarch64-bridge" \
                python3 -B scripts/check_darwin_aarch64_bridge.py \
                    --out "${EVIDENCE_DIR}/darwin-aarch64-bridge" --target-dir "${BRIDGE_TARGET_DIR}"
            ;;
    esac
}

gate_lanes
plan_blockers=$(summary blockers)
if [ -n "${plan_blockers}" ]; then
    printf '%s\n' "${plan_blockers}" | while IFS= read -r blocker; do
        echo "!!! run_public_release_checks: NON-QUALIFYING: ${blocker} !!!" >&2
    done
    if [ "${GATE_MODE}" = require ]; then
        echo "run_public_release_checks: TRUST_CG_PROOF_GATE=require refuses every exclusion and unavailable lane; nothing was run (summary ${SUMMARY})" >&2
        exit 1
    fi
fi
if [ "${DRY_RUN}" -eq 1 ]; then
    GATE_COMPLETED=1
    summary finish --status dry-run >/dev/null
    echo "Public-release anonymous-clone checks: DRY RUN (plan recorded in ${SUMMARY})"
    exit 0
fi

PHASE=run
gate_lanes
GATE_COMPLETED=1
set +e
if [ "${GATE_MODE}" = require ]; then
    verdict=$(summary finish --status pass --require-qualifying)
else
    verdict=$(summary finish --status pass)
fi
finish_status=$?
set -e
if [ "${finish_status}" -ne 0 ]; then
    if [ "${GATE_MODE}" = require ]; then
        echo "run_public_release_checks: FAIL: TRUST_CG_PROOF_GATE=require but the recorded verdict is non-qualifying (summary ${SUMMARY})" >&2
    else
        echo "run_public_release_checks: FAIL: could not record the final verdict (summary ${SUMMARY})" >&2
    fi
    exit 1
fi
if [ "${verdict}" = qualifying ]; then
    echo "Public-release anonymous-clone checks: PASS (TRUST_CG_PROOF_GATE=require, zero exclusions; summary ${SUMMARY})"
else
    echo "!!! run_public_release_checks: this run is NON-QUALIFYING; its exclusions and reasons are in ${SUMMARY} !!!" >&2
    echo "Public-release anonymous-clone checks: PASS (NON-QUALIFYING; summary ${SUMMARY})"
fi
