#!/bin/bash
# scripts/compile_determinism_sentinel.sh — BENCH-8 measurement-determinism sentinel.
#
# THE CLASS: the ay solver deadline is wall-clock (`Instant::now() + timeout_ms` in
# trust-cg-verify/src/ay_bridge.rs), so CPU load can flip a proof verdict to
# inconclusive -> fail-closed reject. The SAME program can then compile on one attempt
# and fail closed on the next — a nondeterministic compile VERDICT that poisons
# coverage% and compile-time series (contract section 7). This sentinel detects that
# flap directly: compile one pinned program N times and compare VERDICTS (not times).
#
# Default mode gives every attempt a FRESH, EMPTY, private user cache root
# (XDG_CACHE_HOME; cold semantics) so every attempt exercises the full solver lane —
# the load-sensitive path — with no certificate, solver-identity or AY copy reused.
# --warm keeps the production warm cache instead (less sensitive: once a verdict is
# cached, later attempts cannot flap; note the invariant that only proven verdicts
# are persisted, so a fail-closed attempt never becomes sticky). The cache is not
# selected with TCG_PROOF_CACHE_DIR: trustc refuses the whole TCG_/TRUST_CG_
# environment family as untracked codegen controls, which failed every attempt.
#
# Exit codes:
#   0 = DETERMINISTIC: all N attempts compiled OK
#   1 = NONDET-FAILCLOSED: verdicts DIFFER across attempts (>=1 OK and >=1 fail-closed)
#       — the load-induced flap class; per-attempt loadavg is printed for diagnosis
#   2 = DETERMINISTIC-FAILCLOSED: all N attempts failed closed — not a nondeterminism
#       finding; the pinned program regressed (completeness) or the dylib is stale
#   3 = CONFIG ERROR: proof gates disabled in env (a sentinel run with gates off
#       proves nothing, and neither does one whose bridge reports its independent
#       proof checker unusable: verification DEGRADED), or missing tooling
#       (including a missing or stale bridge backend)
#
# DRIVER: every compile uses the Trust compiler the bridge pin (channel = "trust")
# names, resolved by scripts/trust_toolchain.py from the PATH trustc/targo package or
# the package trustc named by `--driver PATH`. The retired stock nightly-2026-04-20 and
# any unidentified compiler are refused (exit 3). The frontend runs in Trust's
# explicit unverified lane (-Ztrust-verify=off), a diagnostic lane with no
# Trust-verified compilation claim; the backend proof lane under test is unaffected.
#
# HOSTS: as scripts/compile_time_canary.sh — the target defaults to the resolved
# compiler's host triple (--target overrides) and the backend is the newest current
# librustc_codegen_trust_cg for this host's shared-library suffix
# (scripts/bridge_backend.py) or --dylib; load comes from Python's os.getloadavg.
#
# Usage: scripts/compile_determinism_sentinel.sh [N] [--warm] [--driver PATH]
#                                                [--target TRIPLE] [--dylib PATH]   (default N=5)
set -u

N=5
MODE=cold
TARGET=""
DYLIB=""
DRIVER_ARGS=()
while [ "$#" -gt 0 ]; do
  case "$1" in
    --warm) MODE=warm; shift ;;
    --driver)
      [ "$#" -ge 2 ] || { echo "sentinel: CONFIG ERROR: --driver needs a trustc path" >&2; exit 3; }
      DRIVER_ARGS=(--driver "$2"); shift 2 ;;
    --driver=*) DRIVER_ARGS=(--driver "${1#--driver=}"); shift ;;
    --target)
      [ "$#" -ge 2 ] || { echo "sentinel: CONFIG ERROR: --target needs a triple" >&2; exit 3; }
      TARGET="$2"; shift 2 ;;
    --target=*) TARGET="${1#--target=}"; shift ;;
    --dylib)
      [ "$#" -ge 2 ] || { echo "sentinel: CONFIG ERROR: --dylib needs a backend path" >&2; exit 3; }
      DYLIB="$2"; shift 2 ;;
    --dylib=*) DYLIB="${1#--dylib=}"; shift ;;
    [0-9]*) N="$1"; shift ;;
    *) echo "sentinel: unknown arg $1" >&2; exit 3 ;;
  esac
done

if ! python3 - "$N" <<'PY'
import sys
value = sys.argv[1]
sys.exit(0 if value.isascii() and value.isdecimal() and 0 < int(value) <= sys.maxsize else 1)
PY
then
  echo "sentinel: CONFIG ERROR: attempt count must be a positive, representable integer" >&2
  exit 3
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO="$(dirname "$SCRIPT_DIR")"
export MACOSX_DEPLOYMENT_TARGET="${MACOSX_DEPLOYMENT_TARGET:-13.0}"

# ---- refuse gate-off environments (mirrors compile_time_canary.sh) ----
if [ -n "${TCG_NO_PROOF_CERTS+x}" ]; then
  echo "sentinel: CONFIG ERROR: TCG_NO_PROOF_CERTS is set — the sentinel probes the proof lane. Unset it." >&2
  exit 3
fi
if [ "${TCG_REFINE_SOLVER:-}" = "0" ]; then
  echo "sentinel: CONFIG ERROR: TCG_REFINE_SOLVER=0 — the solver lane IS the nondeterminism source under test. Unset it." >&2
  exit 3
fi

RUSTC="$(python3 "$SCRIPT_DIR/trust_toolchain.py" ${DRIVER_ARGS[@]+"${DRIVER_ARGS[@]}"} --print compiler)" || {
  echo "sentinel: CONFIG ERROR: cannot resolve the pinned Trust compiler" >&2; exit 3; }
DRIVER_SUMMARY="$(python3 "$SCRIPT_DIR/trust_toolchain.py" --driver "$RUSTC" --print summary)" || {
  echo "sentinel: CONFIG ERROR: cannot identify the resolved Trust compiler" >&2; exit 3; }
if [ -z "$TARGET" ]; then
  TARGET="$(python3 "$SCRIPT_DIR/trust_toolchain.py" --driver "$RUSTC" --print host)" || {
    echo "sentinel: CONFIG ERROR: cannot read the Trust compiler's host triple" >&2; exit 3; }
fi
BACKEND_ARGS=(--repo "$REPO" --print path)
[ -n "$DYLIB" ] && BACKEND_ARGS+=(--backend "$DYLIB")
DYLIB="$(python3 "$SCRIPT_DIR/bridge_backend.py" "${BACKEND_ARGS[@]}")" || {
  echo "sentinel: CONFIG ERROR: no current bridge backend (see above)" >&2; exit 3; }
bash "$SCRIPT_DIR/check_benchmark_target.sh" "$RUSTC" "$TARGET" || exit 3

TMP="$(mktemp -d /tmp/tcg-sentinel.XXXXXX)"
trap 'rm -rf "$TMP"' EXIT

# ---- the pinned program (embedded; solver-lane-rich: mul/div/rotate/shift/branch
#      obligations so the wall-clock deadline class is actually reachable) ----
cat > "$TMP/sentinel.rs" <<'RS'
use std::hint::black_box as bb;
fn mix(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b | 1) ^ (a >> 11)
}
fn main() {
    let mut s: u64 = bb(0x243F6A8885A308D3u64);
    let mut acc: u64 = bb(3u64);
    let n = bb(5_000u64);
    let mut i = 0u64;
    while i < n {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        acc = match s % 5 {
            0 => acc.wrapping_add(s),
            1 => mix(acc, s),
            2 => acc.rotate_left((s & 63) as u32),
            3 => acc.wrapping_add(s / ((s & 15) | 1)),
            _ => acc ^ (s >> (s & 31)),
        };
        i += 1;
    }
    std::process::exit((acc % 126) as i32);
}
RS

# Establish that the pinned source and target can compile without the backend.
# Missing std/linker/toolchain prerequisites are not compiler verdict flaps.
if ! python3 "$SCRIPT_DIR/run_with_timeout.py" 60 "$RUSTC" -Ztrust-verify=off --edition=2021 --crate-type bin \
    --target "$TARGET" -Cpanic=abort -Copt-level=3 \
    -o "$TMP/sentinel_reference" "$TMP/sentinel.rs"; then
  echo "sentinel: TOOLING: reference compilation failed; no backend attempts were run" >&2
  exit 3
fi

echo "== compile determinism sentinel: N=$N attempts, mode=$MODE =="
echo "   driver: $DRIVER_SUMMARY"
echo "   dylib: $DYLIB"
# Portable probes (sysctl vm.loadavg / hw.ncpu and shasum are Darwin conventions).
loadavg() { python3 -c 'import os; print(" ".join(f"{x:.2f}" for x in os.getloadavg()))' 2>/dev/null || echo unavailable; }
echo "   target: $TARGET"
echo "   dylib_sha256: $(python3 -c 'import hashlib, sys; print(hashlib.sha256(open(sys.argv[1], "rb").read()).hexdigest())' "$DYLIB")"
echo "   git_sha: $(git -C "$REPO" rev-parse HEAD 2>/dev/null || echo UNRESOLVED)"
echo "   ncpu: $(python3 -c 'import os; print(os.cpu_count())')  loadavg(start): $(loadavg)"

OK=0
FAILED=0
DEGRADED=0
VERDICTS=""
i=1
while [ "$i" -le "$N" ]; do
  LOAD1="$(loadavg | awk '{print $1}')"
  # `env` with no assignments is a no-op wrapper (macOS bash 3.2 + set -u chokes on
  # empty-array expansion, so ENV_ARGS is never empty).
  ENV_ARGS=(env)
  if [ "$MODE" = "cold" ]; then
    # A new, empty, private (0700) user cache root per attempt.
    CACHE_ROOT="$(mktemp -d "$TMP/cache$i.XXXXXX")"
    ENV_ARGS=(env "XDG_CACHE_HOME=$CACHE_ROOT")
  fi
  T0=$(python3 -c 'import time; print(time.monotonic())')
  if "${ENV_ARGS[@]}" "$RUSTC" -Ztrust-verify=off "-Zcodegen-backend=$DYLIB" --edition=2021 --crate-type bin \
      --target "$TARGET" -Cpanic=abort -Copt-level=3 \
      -o "$TMP/sentinel_bin_$i" "$TMP/sentinel.rs" 2>"$TMP/err_$i"; then
    V=OK; OK=$((OK+1))
  else
    V=FAILCLOSED; FAILED=$((FAILED+1))
  fi
  if grep -q "verification is DEGRADED" "$TMP/err_$i"; then
    DEGRADED=$((DEGRADED+1))
  fi
  T1=$(python3 -c 'import time; print(time.monotonic())')
  DT=$(python3 -c "print(f'{$T1-$T0:.2f}')")
  echo "   attempt $i: $V  (${DT}s, 1-min loadavg $LOAD1)"
  if [ "$V" = FAILCLOSED ]; then
    # print the error banner AND the per-function detail lines (the '- fn: reason' lines)
    grep -E '^error|^\s+- ' "$TMP/err_$i" | sed 's/^/     /' | head -6
    cp "$TMP/err_$i" "/tmp/tcg-sentinel-failclosed-attempt$i.err" 2>/dev/null || true
    echo "     (full stderr preserved: /tmp/tcg-sentinel-failclosed-attempt$i.err)"
  fi
  VERDICTS="$VERDICTS $V"
  i=$((i+1))
done

echo "   verdicts:$VERDICTS  loadavg(end): $(loadavg)"

if [ "$DEGRADED" -gt 0 ]; then
  echo "sentinel: CONFIG ERROR: $DEGRADED attempt(s) reported the independent proof checker UNUSABLE (verification DEGRADED); their verdicts are not the production proof lane's — provision a capable Clean package prefix on PATH" >&2
  exit 3
fi

if [ "$OK" -eq "$N" ]; then
  echo "sentinel: DETERMINISTIC — all $N compiles succeeded"
  exit 0
fi
if [ "$FAILED" -eq "$N" ]; then
  echo "sentinel: DETERMINISTIC-FAILCLOSED — all $N attempts failed closed. Not a flap:" >&2
  echo "sentinel: the pinned program regressed (completeness) or the dylib is stale — investigate." >&2
  exit 2
fi
echo "sentinel: *** NONDET-FAILCLOSED *** verdicts differ ($OK OK / $FAILED fail-closed of $N)." >&2
echo "sentinel: load-sensitive solver wall-clock deadline class (ay_bridge.rs 'Instant::now() + timeout')." >&2
echo "sentinel: per-attempt loadavg above; rerun on a quiet machine before trusting any coverage%/compile datum." >&2
exit 1
