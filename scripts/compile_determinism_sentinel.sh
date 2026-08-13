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
# Default mode uses a FRESH proof-cache dir per attempt (cold semantics) so every
# attempt exercises the full solver lane — the load-sensitive path. --warm keeps the
# production warm cache instead (less sensitive: once a verdict is cached, later
# attempts cannot flap; note the invariant that only proven verdicts are persisted,
# so a fail-closed attempt never becomes sticky).
#
# Exit codes:
#   0 = DETERMINISTIC: all N attempts compiled OK
#   1 = NONDET-FAILCLOSED: verdicts DIFFER across attempts (>=1 OK and >=1 fail-closed)
#       — the load-induced flap class; per-attempt loadavg is printed for diagnosis
#   2 = DETERMINISTIC-FAILCLOSED: all N attempts failed closed — not a nondeterminism
#       finding; the pinned program regressed (completeness) or the dylib is stale
#   3 = CONFIG ERROR: proof gates disabled in env (a sentinel run with gates off
#       proves nothing), or missing tooling
#
# Usage: scripts/compile_determinism_sentinel.sh [N] [--warm]   (default N=5)
set -u

N=5
MODE=cold
for a in "$@"; do
  case "$a" in
    --warm) MODE=warm ;;
    [0-9]*) N="$a" ;;
    *) echo "sentinel: unknown arg $a" >&2; exit 3 ;;
  esac
done

TOOLCHAIN=nightly-2026-04-20
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO="$(dirname "$SCRIPT_DIR")"
DYLIB="$REPO/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
export PATH="$HOME/.cargo/bin:$PATH"
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

RUSTC="$(rustup which --toolchain "$TOOLCHAIN" rustc 2>/dev/null)" || {
  echo "sentinel: CONFIG ERROR: cannot resolve rustc for $TOOLCHAIN" >&2; exit 3; }
[ -f "$DYLIB" ] || { echo "sentinel: CONFIG ERROR: bridge dylib missing: $DYLIB" >&2; exit 3; }

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

echo "== compile determinism sentinel: N=$N attempts, mode=$MODE =="
echo "   dylib: $DYLIB"
echo "   dylib_sha256: $(shasum -a 256 "$DYLIB" | awk '{print $1}')"
echo "   git_sha: $(git -C "$REPO" rev-parse HEAD 2>/dev/null || echo UNRESOLVED)"
echo "   ncpu: $(sysctl -n hw.ncpu)  loadavg(start): $(sysctl -n vm.loadavg)"

OK=0
FAILED=0
VERDICTS=""
i=1
while [ "$i" -le "$N" ]; do
  LOAD1="$(sysctl -n vm.loadavg | awk '{print $2}')"
  # `env` with no assignments is a no-op wrapper (macOS bash 3.2 + set -u chokes on
  # empty-array expansion, so ENV_ARGS is never empty).
  ENV_ARGS=(env)
  if [ "$MODE" = "cold" ]; then
    mkdir -p "$TMP/cache$i"
    ENV_ARGS=(env "TCG_PROOF_CACHE_DIR=$TMP/cache$i")
  fi
  T0=$(python3 -c 'import time; print(time.monotonic())')
  if "${ENV_ARGS[@]}" "$RUSTC" "-Zcodegen-backend=$DYLIB" --edition=2021 --crate-type bin \
      --target x86_64-apple-darwin -Cpanic=abort -Copt-level=3 \
      -o "$TMP/sentinel_bin_$i" "$TMP/sentinel.rs" 2>"$TMP/err_$i"; then
    V=OK; OK=$((OK+1))
  else
    V=FAILCLOSED; FAILED=$((FAILED+1))
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

echo "   verdicts:$VERDICTS  loadavg(end): $(sysctl -n vm.loadavg)"

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
