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
#     sessions don't false-red the gate. The threshold is the THRESHOLD_S literal in
#     THIS script — there is no ratchet/ baseline file for it (ratchet/ holds the
#     BENCH-5 perf ratchet, ratchet/perf_baseline.json, consumed by
#     scripts/check_perf_ratchet.py, not this canary). It TIGHTENS as the G2 climb
#     progresses by lowering that literal in an explicit reviewed commit, never an
#     in-run adjustment, and is renegotiated BEFORE any cap-lifting change flips on.
#   - The same literal applies on every host: it is a cliff alarm for the
#     ~16s/process class, not a parity gate. No quiet Linux AArch64 calibration has
#     been recorded yet.
#
# GATE-OFF RUNS ARE NOT EVIDENCE: this script REFUSES to run (exit 3) if
# TCG_NO_PROOF_CERTS is set, or if TCG_REFINE_SOLVER=0 / TCG_NO_PROOF_CACHE would
# change the measured lane. A canary pass with the gates disabled proves nothing.
#
# Exit codes (the `targo --unverified run -p trust-cg-test --quiet -- ratchet tests` convention):
#   0 = OK (median <= threshold, exit codes match LLVM)
#   1 = GATE RED: threshold breached on a quiet machine, or exit-code MISMATCH (P0)
#   2 = TOOLING/INCONCLUSIVE: missing or stale dylib, missing toolchain, or breach while 1-min load > ncpu
#       (machine noise is never converted into a red gate — rerun on a quiet machine)
#   3 = CONFIG ERROR: proof gates disabled in the environment (including a bridge that
#       reports its independent proof checker unusable: verification DEGRADED, unless
#       the binaries' exit codes MISMATCH, which is 1 in any configuration), or a
#       bad argument
#
# DRIVER: both lanes use the Trust compiler the bridge pin (channel = "trust") names,
# resolved by scripts/trust_toolchain.py from the PATH trustc/targo package, or the
# package trustc named by `--driver PATH`. The retired stock nightly-2026-04-20 and
# any unidentified compiler are refused (exit 2). The frontend runs in Trust's
# explicit unverified lane (-Ztrust-verify=off), matching the vanilla frontend the
# canary always measured; that lane is diagnostic and makes no Trust-verified
# compilation claim. The backend proof gates above are unaffected.
#
# HOSTS: the canary runs wherever the Trust package and its bridge run (Darwin and
# Linux, x86_64 and AArch64). The target defaults to the resolved compiler's host
# triple (--target overrides). The backend is the newest built
# librustc_codegen_trust_cg with this host's shared-library suffix (.dylib on Darwin,
# .so on Linux) among the build locations scripts/bridge_backend.py lists, or
# --dylib; a missing or STALE backend (a backend source newer than it) is TOOLING
# (exit 2), because timing an old backend would report on code that is not in the
# tree. Load and CPU count come from Python's os.getloadavg/os.cpu_count and hashes
# from hashlib, so no Darwin-only sysctl or shasum is needed.
#
# Usage: scripts/compile_time_canary.sh [--driver <trust-package>/bin/trustc]
#                                        [--target TRIPLE] [--dylib PATH]
set -u

THRESHOLD_S=8
EXPECTED_EXIT=51   # pinned: full-width checksum of the xorshift loop, mod 126
TARGET=""
DYLIB=""

DRIVER_ARGS=()
while [ "$#" -gt 0 ]; do
  case "$1" in
    --driver)
      [ "$#" -ge 2 ] || { echo "canary: CONFIG ERROR: --driver needs a trustc path" >&2; exit 3; }
      DRIVER_ARGS=(--driver "$2"); shift 2 ;;
    --driver=*) DRIVER_ARGS=(--driver "${1#--driver=}"); shift ;;
    --target)
      [ "$#" -ge 2 ] || { echo "canary: CONFIG ERROR: --target needs a triple" >&2; exit 3; }
      TARGET="$2"; shift 2 ;;
    --target=*) TARGET="${1#--target=}"; shift ;;
    --dylib)
      [ "$#" -ge 2 ] || { echo "canary: CONFIG ERROR: --dylib needs a backend path" >&2; exit 3; }
      DYLIB="$2"; shift 2 ;;
    --dylib=*) DYLIB="${1#--dylib=}"; shift ;;
    *) echo "canary: CONFIG ERROR: unknown argument $1 (usage: [--driver PATH] [--target TRIPLE] [--dylib PATH])" >&2; exit 3 ;;
  esac
done

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO="$(dirname "$SCRIPT_DIR")"
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
RUSTC="$(python3 "$SCRIPT_DIR/trust_toolchain.py" ${DRIVER_ARGS[@]+"${DRIVER_ARGS[@]}"} --print compiler)" || {
  echo "canary: TOOLING: cannot resolve the pinned Trust compiler" >&2; exit 2; }
DRIVER_SUMMARY="$(python3 "$SCRIPT_DIR/trust_toolchain.py" --driver "$RUSTC" --print summary)" || {
  echo "canary: TOOLING: cannot identify the resolved Trust compiler" >&2; exit 2; }
if [ -z "$TARGET" ]; then
  TARGET="$(python3 "$SCRIPT_DIR/trust_toolchain.py" --driver "$RUSTC" --print host)" || {
    echo "canary: TOOLING: cannot read the Trust compiler's host triple" >&2; exit 2; }
fi
BACKEND_ARGS=(--repo "$REPO" --print path)
[ -n "$DYLIB" ] && BACKEND_ARGS+=(--backend "$DYLIB")
DYLIB="$(python3 "$SCRIPT_DIR/bridge_backend.py" "${BACKEND_ARGS[@]}")" || {
  echo "canary: TOOLING: no current bridge backend (see above); build it before timing it" >&2; exit 2; }
bash "$SCRIPT_DIR/check_benchmark_target.sh" "$RUSTC" "$TARGET" || exit 2

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
# The Alethe certificate store is the persistent reuse tier the warm lane reads
# (trust-cg-verify obligation_cert_store::store_dir); the verdict directory
# above is legacy and stays empty.
CERT_DIR="${XDG_CACHE_HOME:-$HOME/.cache}/trust-cg/alethe-certs"
certs() { ls "$CERT_DIR" 2>/dev/null | grep -c '\.alethecert$' || true; }
C_BEFORE="$(certs)"

# -Ztrust-verify=off: Trust's explicit unverified frontend lane (see DRIVER above).
RUSTC_ARGS=(-Ztrust-verify=off --edition=2021 --crate-type bin --target "$TARGET" -Cpanic=abort -Copt-level=3)

DEGRADED_LOG="$TMP/degraded"
time_compile() { # prints seconds; nonzero on compile failure
  CANARY_DEGRADED_LOG="$DEGRADED_LOG" python3 - "$@" <<'PY'
import os, subprocess, sys, time
t0 = time.monotonic()
r = subprocess.run(sys.argv[1:], capture_output=True, text=True)
dt = time.monotonic() - t0
# trust-cg-verify's banner for an unusable independent proof checker: the
# backend then runs a degraded proof lane, which is not what this canary times.
if "verification is DEGRADED" in r.stderr:
    with open(os.environ["CANARY_DEGRADED_LOG"], "a") as log:
        log.write("degraded\n")
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
# A degraded proof checker outranks every TIMING and completeness verdict:
# neither a pass nor a compile failure of a degraded lane says anything about
# the production lane. It never outranks a wrong-code MISMATCH, which is P0 in
# any configuration (checked first, below).
refuse_if_degraded() {
  if [ -s "$DEGRADED_LOG" ]; then
    echo "canary: CONFIG ERROR: the bridge reported its independent proof checker UNUSABLE (verification DEGRADED) — a degraded proof lane is not the production lane this canary times; provision a capable Clean package prefix on PATH" >&2
    exit 3
  fi
}
bridge_failed() {
  refuse_if_degraded
  echo "canary: GATE RED: bridge failed to compile the pinned canary program (fail-closed or ICE)" >&2
  exit 1
}
time_compile "${BRIDGE[@]}" > /dev/null || bridge_failed
T1="$(time_compile "${BRIDGE[@]}")" || bridge_failed
T2="$(time_compile "${BRIDGE[@]}")" || bridge_failed
T3="$(time_compile "${BRIDGE[@]}")" || bridge_failed
MEDIAN="$(printf '%s\n%s\n%s\n' "$T1" "$T2" "$T3" | sort -n | sed -n '2p')"
V_AFTER="$(verdicts)"
C_AFTER="$(certs)"

# ---- correctness: a fast wrong compile is a failure, never a datum ----
"$TMP/canary_llvm";   LLVM_EXIT=$?
"$TMP/canary_bridge"; BRIDGE_EXIT=$?

# ---- provenance stamp (numbers without stamps are not evidence) ----
# Portable probes: Python's os.getloadavg/os.cpu_count and hashlib behave the same on
# Darwin and Linux (sysctl vm.loadavg / hw.ncpu and shasum are Darwin conventions).
sha256_stdin() { python3 -c 'import hashlib, sys; print(hashlib.sha256(sys.stdin.buffer.read()).hexdigest())'; }
GIT_SHA="$(git -C "$REPO" rev-parse HEAD 2>/dev/null || echo UNRESOLVED)"
DIRTY="clean"; [ -n "$(git -C "$REPO" status --porcelain 2>/dev/null | grep -v '^??')" ] && DIRTY="dirty"
DIFF_SHA="$(git -C "$REPO" diff HEAD 2>/dev/null | sha256_stdin)"
DYLIB_SHA="$(sha256_stdin < "$DYLIB")"
LOAD1="$(python3 -c 'import os; print(f"{os.getloadavg()[0]:.2f}")')" || LOAD1=""
NCPU="$(python3 -c 'import os; print(os.cpu_count() or "")')" || NCPU=""
TCG_ENV="$(env | grep -E '^(TCG_|TRUST_CG_)' | tr '\n' ' ')"
echo "== compile-time canary provenance =="
echo "  git_sha:        $GIT_SHA ($DIRTY, diff_sha256=$DIFF_SHA)"
echo "  dylib:          $DYLIB"
echo "  dylib_sha256:   $DYLIB_SHA"
echo "  trustc:         $("$RUSTC" --version) [$RUSTC]"
echo "  driver:         $DRIVER_SUMMARY"
echo "  tcg_env:        ${TCG_ENV:-<production defaults>}"
echo "  cache (warm):   $CACHE_DIR verdicts ${V_BEFORE}->${V_AFTER}; $CERT_DIR certificates ${C_BEFORE}->${C_AFTER}"
echo "  target:         $TARGET"
echo "  loadavg_1min:   $LOAD1 (ncpu=$NCPU)"
echo "  llvm -O3:       ${LLVM_T}s (exit $LLVM_EXIT)"
echo "  bridge warm:    $T1 $T2 $T3 -> median ${MEDIAN}s (exit $BRIDGE_EXIT)"
echo "  threshold:      ${THRESHOLD_S}s (baseline ~1.8s warm certs-on @ 0456e2a; tightens by reviewed commit to THRESHOLD_S)"

# Wrong code first: a MISMATCH is P0 whatever the proof checker's state.
if [ "$BRIDGE_EXIT" -ne "$LLVM_EXIT" ] || [ "$BRIDGE_EXIT" -ne "$EXPECTED_EXIT" ]; then
  [ -s "$DEGRADED_LOG" ] && echo "canary: note: the bridge also reported verification DEGRADED; wrong code is P0 regardless" >&2
  echo "canary: GATE RED: exit-code MISMATCH (llvm=$LLVM_EXIT bridge=$BRIDGE_EXIT expected=$EXPECTED_EXIT) — P0 stop-the-line" >&2
  exit 1
fi
refuse_if_degraded

if awk "BEGIN{exit !($MEDIAN <= $THRESHOLD_S)}"; then
  echo "canary: OK (median ${MEDIAN}s <= ${THRESHOLD_S}s, exit codes match)"
  exit 0
fi

# Breach: never convert machine noise into a red gate (roadmap BENCH-4). A load
# that cannot be read cannot excuse a breach either: the breach stays RED.
if [ -n "$LOAD1" ] && [ -n "$NCPU" ] && awk -v load="$LOAD1" -v ncpu="$NCPU" 'BEGIN{exit !(load > ncpu)}'; then
  echo "canary: INCONCLUSIVE: median ${MEDIAN}s > ${THRESHOLD_S}s but 1-min load $LOAD1 > ncpu=$NCPU — rerun on a quiet machine" >&2
  exit 2
fi
echo "canary: GATE RED: warm compile median ${MEDIAN}s > ${THRESHOLD_S}s — compile-time regression (do not loosen this threshold; find the regression)" >&2
exit 1
