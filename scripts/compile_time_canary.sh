#!/bin/bash
# scripts/compile_time_canary.sh — BENCH-4 compile-time canary (hard threshold).
#
# Compiles ONE pinned small scalar program through the release bridge dylib with the
# PRODUCTION default gates (certs ON, solver refinement ON, verdict cache ON) and fails
# if the WARM median-of-3 wall time exceeds the threshold. This is the alarm that makes
# a popcnt-canary-class compile-time regression (~16s/process, went unnoticed) or a
# GreedyAllocator::interferes blowup structurally impossible to land silently.
#
# CALIBRATION (documented per metrics-contract.md §3):
#   - Measured warm certs-on baseline at 0456e2a on the x86 Mac (quiet): ~1.8s.
#   - THRESHOLD_S=8: ~4.4x headroom, deliberately load-tolerant so parallel executor
#     sessions don't false-red the gate. It TIGHTENS later via ratchet commits
#     (ratchet/compile_time_baseline.json, the check_test_ratchet.sh convention) as the
#     G2 climb progresses — threshold changes are explicit reviewed commits, never
#     in-run adjustments, and are renegotiated BEFORE any cap-lifting change flips on.
#
# GATE-OFF RUNS ARE NOT EVIDENCE: this script REFUSES to run (exit 3) if
# TCG_NO_PROOF_CERTS is set, or if TCG_REFINE_SOLVER=0 / TCG_NO_PROOF_CACHE would
# change the measured lane. A canary pass with the gates disabled proves nothing.
#
# Exit codes (check_test_ratchet.sh convention):
#   0 = OK (median <= threshold, exit codes match LLVM)
#   1 = GATE RED: threshold breached on a quiet machine, or exit-code MISMATCH (P0)
#   2 = TOOLING/INCONCLUSIVE: missing dylib/toolchain, or breach while 1-min load > ncpu
#       (machine noise is never converted into a red gate — rerun on a quiet machine)
#   3 = CONFIG ERROR: proof gates disabled in the environment
set -u

THRESHOLD_S=8
EXPECTED_EXIT=51   # pinned: full-width checksum of the xorshift loop, mod 126
TOOLCHAIN=nightly-2026-04-20

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO="$(dirname "$SCRIPT_DIR")"
DYLIB="$REPO/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
export PATH="$HOME/.cargo/bin:$PATH"
export MACOSX_DEPLOYMENT_TARGET="${MACOSX_DEPLOYMENT_TARGET:-13.0}"

# ---- refuse gate-off environments (a canary run with gates off is not evidence) ----
if [ -n "${TCG_NO_PROOF_CERTS+x}" ]; then
  echo "canary: CONFIG ERROR: TCG_NO_PROOF_CERTS is set — a canary run with proof certs off is not evidence. Unset it." >&2
  exit 3
fi
if [ "${TCG_REFINE_SOLVER:-}" = "0" ]; then
  echo "canary: CONFIG ERROR: TCG_REFINE_SOLVER=0 — the canary measures the default certs+solver lane. Unset it." >&2
  exit 3
fi
if [ -n "${TCG_NO_PROOF_CACHE+x}" ]; then
  echo "canary: CONFIG ERROR: TCG_NO_PROOF_CACHE is set — the canary measures the WARM lane (dde503a cache on). Unset it." >&2
  exit 3
fi

# ---- tooling ----
RUSTC="$(rustup which --toolchain "$TOOLCHAIN" rustc 2>/dev/null)" || {
  echo "canary: TOOLING: cannot resolve rustc for $TOOLCHAIN" >&2; exit 2; }
[ -f "$DYLIB" ] || { echo "canary: TOOLING: bridge dylib missing: $DYLIB" >&2; exit 2; }

TMP="$(mktemp -d /tmp/tcg-canary.XXXXXX)"
trap 'rm -rf "$TMP"' EXIT

# ---- the pinned program (embedded so corpus edits can never move the canary) ----
cat > "$TMP/canary.rs" <<'RS'
use std::hint::black_box as bb;
fn main() {
    let mut x: u64 = bb(0x9E3779B97F4A7C15u64);
    let mut acc: u64 = 0;
    let mut i: u64 = 0;
    let n = bb(10_000u64);
    while i < n {
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        acc = acc.wrapping_add(x ^ i);
        i += 1;
    }
    std::process::exit((acc % 126) as i32);
}
RS

CACHE_DIR="${TCG_PROOF_CACHE_DIR:-$HOME/.cache/trust-cg/proof-cache}"
verdicts() { ls "$CACHE_DIR" 2>/dev/null | grep -c '\.verdict$' || true; }
V_BEFORE="$(verdicts)"

RUSTC_ARGS=(--edition=2021 --crate-type bin --target x86_64-apple-darwin -Cpanic=abort -Copt-level=3)

time_compile() { # prints seconds; nonzero on compile failure
  python3 - "$@" <<'PY'
import subprocess, sys, time
t0 = time.monotonic()
r = subprocess.run(sys.argv[1:], capture_output=True, text=True)
dt = time.monotonic() - t0
if r.returncode != 0:
    sys.stderr.write(r.stderr[-2000:] + "\n")
    sys.exit(1)
print(f"{dt:.3f}")
PY
}

# ---- LLVM lane (differential exit-code oracle; also a -O3 compile-time reference) ----
LLVM_T="$(time_compile "$RUSTC" "${RUSTC_ARGS[@]}" -o "$TMP/canary_llvm" "$TMP/canary.rs")" || {
  echo "canary: TOOLING: LLVM lane failed to compile the pinned program" >&2; exit 2; }

# ---- bridge WARM lane: 1 unmeasured warmup (populates the verdict cache), then median-of-3 ----
BRIDGE=("$RUSTC" "-Zcodegen-backend=$DYLIB" "${RUSTC_ARGS[@]}" -o "$TMP/canary_bridge" "$TMP/canary.rs")
time_compile "${BRIDGE[@]}" > /dev/null || {
  echo "canary: GATE RED: bridge failed to compile the pinned canary program (fail-closed or ICE)" >&2; exit 1; }
T1="$(time_compile "${BRIDGE[@]}")" || exit 1
T2="$(time_compile "${BRIDGE[@]}")" || exit 1
T3="$(time_compile "${BRIDGE[@]}")" || exit 1
MEDIAN="$(printf '%s\n%s\n%s\n' "$T1" "$T2" "$T3" | sort -n | sed -n '2p')"
V_AFTER="$(verdicts)"

# ---- correctness: a fast wrong compile is a failure, never a datum ----
"$TMP/canary_llvm";   LLVM_EXIT=$?
"$TMP/canary_bridge"; BRIDGE_EXIT=$?

# ---- provenance stamp (numbers without stamps are not evidence) ----
GIT_SHA="$(git -C "$REPO" rev-parse HEAD 2>/dev/null || echo UNRESOLVED)"
DIRTY="clean"; [ -n "$(git -C "$REPO" status --porcelain 2>/dev/null | grep -v '^??')" ] && DIRTY="dirty"
DIFF_SHA="$(git -C "$REPO" diff HEAD 2>/dev/null | shasum -a 256 | awk '{print $1}')"
DYLIB_SHA="$(shasum -a 256 "$DYLIB" | awk '{print $1}')"
LOAD1="$(sysctl -n vm.loadavg | awk '{print $2}')"
NCPU="$(sysctl -n hw.ncpu)"
TCG_ENV="$(env | grep -E '^(TCG_|TRUST_CG_)' | tr '\n' ' ')"
echo "== compile-time canary provenance =="
echo "  git_sha:        $GIT_SHA ($DIRTY, diff_sha256=$DIFF_SHA)"
echo "  dylib:          $DYLIB"
echo "  dylib_sha256:   $DYLIB_SHA"
echo "  rustc:          $("$RUSTC" --version) [$RUSTC]"
echo "  tcg_env:        ${TCG_ENV:-<production defaults>}"
echo "  cache (warm):   $CACHE_DIR verdicts ${V_BEFORE}->${V_AFTER}"
echo "  loadavg_1min:   $LOAD1 (ncpu=$NCPU)"
echo "  llvm -O3:       ${LLVM_T}s (exit $LLVM_EXIT)"
echo "  bridge warm:    $T1 $T2 $T3 -> median ${MEDIAN}s (exit $BRIDGE_EXIT)"
echo "  threshold:      ${THRESHOLD_S}s (baseline ~1.8s warm certs-on @ 0456e2a; tightens by ratchet)"

if [ "$BRIDGE_EXIT" -ne "$LLVM_EXIT" ] || [ "$BRIDGE_EXIT" -ne "$EXPECTED_EXIT" ]; then
  echo "canary: GATE RED: exit-code MISMATCH (llvm=$LLVM_EXIT bridge=$BRIDGE_EXIT expected=$EXPECTED_EXIT) — P0 stop-the-line" >&2
  exit 1
fi

if awk "BEGIN{exit !($MEDIAN <= $THRESHOLD_S)}"; then
  echo "canary: OK (median ${MEDIAN}s <= ${THRESHOLD_S}s, exit codes match)"
  exit 0
fi

# Breach: never convert machine noise into a red gate (roadmap BENCH-4).
if awk "BEGIN{exit !($LOAD1 > $NCPU)}"; then
  echo "canary: INCONCLUSIVE: median ${MEDIAN}s > ${THRESHOLD_S}s but 1-min load $LOAD1 > ncpu=$NCPU — rerun on a quiet machine" >&2
  exit 2
fi
echo "canary: GATE RED: warm compile median ${MEDIAN}s > ${THRESHOLD_S}s — compile-time regression (do not loosen this threshold; find the regression)" >&2
exit 1
