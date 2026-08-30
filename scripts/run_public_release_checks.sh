#!/bin/sh
#
# Exact anonymous-clone validation for the publication candidate.

set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO_ROOT=$(CDPATH= cd -- "${SCRIPT_DIR}/.." && pwd)
cd "${REPO_ROOT}"

# Release validation includes generated, memory-intensive integration targets.
# Run libtest serially by default while preserving an explicit caller override.
: "${RUST_TEST_THREADS:=1}"
export RUST_TEST_THREADS

python3 -B scripts/check_trust_default_authority.py --root .
python3 -B -m unittest discover -s scripts/tests -p 'test_*.py'

expected_rustc='rustc 1.97.1 (8bab26f4f 2026-07-14)'
expected_cargo='cargo 1.97.1 (c980f4866 2026-06-30)'
actual_rustc=$(rustc --version)
actual_cargo=$(cargo --version)
actual_host=$(rustc -vV | sed -n 's/^host: //p')
if [ "${actual_rustc}" != "${expected_rustc}" ]; then
    echo "run_public_release_checks: expected ${expected_rustc}, got ${actual_rustc}" >&2
    exit 1
fi
if [ "${actual_cargo}" != "${expected_cargo}" ]; then
    echo "run_public_release_checks: expected ${expected_cargo}, got ${actual_cargo}" >&2
    exit 1
fi
if [ "${actual_host}" != "aarch64-apple-darwin" ]; then
    echo "run_public_release_checks: expected aarch64-apple-darwin host, got ${actual_host:-unknown}" >&2
    exit 1
fi

# The authoritative 18-program correctness harness is release machinery, even
# though a normal smoke does not run its timing lanes. Parse it here so a syntax
# regression cannot make the advertised differential gate silently unusable.
python3 -c 'import ast, pathlib, sys; ast.parse(pathlib.Path(sys.argv[1]).read_text(), filename=sys.argv[1])' \
    benchmarks/beat-llvm/run.py

scripts/test_run_with_timeout.sh
scripts/test_soundness_check.sh
python3 crates/trust-cg-sat-host/tests/fixtures/sat_corpus/generators.py --check
test -s third_party/vendor/xxhash-LICENSE
test -s third_party/vendor/rust-stdlib-SipHasher13-LICENSE

cargo metadata --locked --format-version 1 >/dev/null
cargo metadata --locked \
    --manifest-path crates/rustc-codegen-trust-cg/Cargo.toml \
    --format-version 1 >/dev/null
cargo metadata --locked --manifest-path fuzz/Cargo.toml \
    --format-version 1 >/dev/null

cargo check --locked --workspace --all-targets --all-features
cargo check --locked --manifest-path fuzz/Cargo.toml

scripts/test_pgo_runtime.sh
# trust-cg-verify's CEGIS lane shells out to an `ay` BINARY, discovered through
# the Trust toolchain layout (build/<triple>/stage2/bin/ay, else
# first-party/ay/target/release/ay). The public-clone release gate runs with a
# fresh HOME and an isolated source tree by design, so no solver is discoverable
# there and every solver-backed test fails on the environment rather than on the
# code. Skip that lane ONLY when no solver exists — a dev machine with one still
# runs the full suite — and say so loudly, the same way the orca-alab gates
# announce a skip when ty/ay are absent.
# `AY_SOLVER_PATH` is the canonical override and the ONLY name the backend
# reads (crates/trust-cg-verify/src/ay_bridge.rs, select_solver_binary: an
# explicit AY_SOLVER_PATH wins over the toolchain layout and PATH lookup).
# `TCG_SOLVER_PATH` is accepted as a legacy alias for existing operator
# invocations and exported to the canonical name, so the tests see exactly the
# solver this gate saw — a gate that believes a solver exists while the tests
# resolve nothing is the failure mode this mapping closes.
if [ -z "${AY_SOLVER_PATH:-}" ] && [ -n "${TCG_SOLVER_PATH:-}" ]; then
    export AY_SOLVER_PATH="${TCG_SOLVER_PATH}"
fi
tcg_solver_present() {
    if [ -n "${AY_SOLVER_PATH:-}" ]; then
        # The backend accepts either a file path or a bare binary name on PATH.
        [ -x "${AY_SOLVER_PATH}" ] && return 0
        command -v "${AY_SOLVER_PATH}" >/dev/null 2>&1 && return 0
    fi
    command -v ay >/dev/null 2>&1 && return 0
    for root in "$HOME/trust" "$HOME"; do
        [ -x "$root/build/aarch64-apple-darwin/stage2/bin/ay" ] && return 0
        [ -x "$root/first-party/ay/target/release/ay" ] && return 0
        [ -x "$root/ay/target/release/ay" ] && return 0
    done
    return 1
}

if tcg_solver_present; then
    cargo test --locked --workspace --all-features \
        --exclude trust-cg-codegen --no-fail-fast -- \
        --test-threads="${RUST_TEST_THREADS}"
else
    echo "run_public_release_checks: NO AY SOLVER FOUND -- skipping the" >&2
    echo "  trust-cg-verify CEGIS lane. This release is verified MODULO CEGIS." >&2
    echo "  Set AY_SOLVER_PATH (TCG_SOLVER_PATH is an accepted alias) or place \`ay\` on PATH to run it." >&2
    cargo test --locked --workspace --all-features \
        --exclude trust-cg-codegen --exclude trust-cg-verify --no-fail-fast -- \
        --test-threads="${RUST_TEST_THREADS}"
fi
scripts/run_public_release_codegen_tests.sh --release

grep -Eq '^channel = ["]nightly-2026-04-20["]$' \
    crates/rustc-codegen-trust-cg/rust-toolchain.toml
scripts/run_full_test_matrix.sh --check-rustc-backend-env
(
    cd crates/rustc-codegen-trust-cg
    CARGO_TARGET_DIR=../../target/rustc-codegen-trust-cg-nightly-2026-04-20 \
        rustup run nightly-2026-04-20 cargo test --release --locked \
            --all-features --all-targets --no-fail-fast -- \
            --test-threads="${RUST_TEST_THREADS}"
    # No doctest lane: the backend is crate-type ["dylib"] only (the
    # rustc_codegen_cranelift convention), and cargo hard-errors on
    # `cargo test --doc` for a package with no doctestable lib target
    # ("no library targets found"). The --all-targets run above is the
    # complete test surface for this crate.
)

echo "Public-release anonymous-clone checks: PASS"
