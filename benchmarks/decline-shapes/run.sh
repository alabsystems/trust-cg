#!/usr/bin/env bash
# Minimal named shapes for the [TCG-SSA-071] decline class.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# WHY: ~38% of generated safe Rust fails closed, and essentially all of it is
# ONE diagnostic. This pins the boundary as minimal programs so the gap is
# measurable instead of a percentage:
#
#   d_*   currently DECLINE  — each should flip to a MATCH when the class is fixed
#   ok_*  currently COMPILE  — the near-miss neighbours; they must NEVER regress
#
# Every program is UB-free, deterministic, and encodes its answer in its exit
# status, with trustc's LLVM backend as the oracle. A d_* that starts compiling is
# progress; an ok_* that starts declining, or any WRONG-ANSWER, is a regression.
#
# Both sides use the Trust compiler the bridge pin (channel = "trust") names,
# resolved by scripts/trust_toolchain.py from the PATH trustc/targo package or
# the package trustc named by --driver. The retired stock nightly, any
# unidentified compiler and a bare `rustc` fallback are refused (exit 2). Both
# sides compile in Trust's explicit unverified frontend lane (-Ztrust-verify=off),
# a diagnostic lane with no Trust-verified compilation claim.
#
# Usage: ./run.sh [--driver TRUSTC]   (env DECLINE_DYLIB, DECLINE_OUT)
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
DRIVER_ARGS=()
if [ "${1:-}" = "--driver" ]; then
  [ "$#" -ge 2 ] || { echo "decline-shapes: --driver needs a trustc path" >&2; exit 2; }
  DRIVER_ARGS=(--driver "$2"); shift 2
fi
DYLIB="${DECLINE_DYLIB:-$HERE/../../crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so}"
OUT="${DECLINE_OUT:-$(mktemp -d)}"; mkdir -p "$OUT"
# STOCK EXCEPTION (Trust lacks rust-lld/gcc-ld; measured: no lib/rustlib/<host>/bin/{rust-lld,gcc-ld} in the Trust sysroot): the Linux linker shim comes from the stock stable toolchain's gcc-ld; the compilers come from scripts/trust_toolchain.py.
export PATH="$HOME/.rustup/toolchains/stable-aarch64-unknown-linux-gnu/lib/rustlib/aarch64-unknown-linux-gnu/bin/gcc-ld:$PATH"
RUSTC="$(python3 "$HERE/../../scripts/trust_toolchain.py" ${DRIVER_ARGS[@]+"${DRIVER_ARGS[@]}"} --print compiler)" || {
  echo "decline-shapes: cannot resolve the pinned Trust compiler" >&2; exit 2; }
echo "decline-shapes: driver $(python3 "$HERE/../../scripts/trust_toolchain.py" --driver "$RUSTC" --print summary)"
B="-Ztrust-verify=off --edition=2021 --crate-type bin -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1 -Cdefault-linker-libraries=y"
declined=0; compiled=0; wrong=0; regressed=0; progressed=0
for f in "$HERE"/progs/*.rs; do
  n=$(basename "$f" .rs); exp=${n%%_*}
  "$RUSTC" $B -Copt-level=2 -o "$OUT/l_$n" "$f" 2>/dev/null || { echo "ORACLE-FAIL $n"; continue; }
  "$OUT/l_$n" >/dev/null 2>&1; want=$?
  if "$RUSTC" $B -Ztrust-ir-cg-args=no-proof-certs -Ztrust-ir-cg-args=refine-solver=0 -Copt-level=2 \
       -Zcodegen-backend="$DYLIB" -o "$OUT/t_$n" "$f" 2>"$OUT/$n.err"; then
    "$OUT/t_$n" >/dev/null 2>&1; got=$?
    compiled=$((compiled+1))
    if [ "$got" != "$want" ]; then
      wrong=$((wrong+1)); echo "WRONG-ANSWER $n: want $want got $got"
    elif [ "$exp" = "d" ]; then
      progressed=$((progressed+1)); echo "PROGRESS $n now compiles and MATCHES (was a tracked decline)"
    fi
  else
    declined=$((declined+1))
    if [ "$exp" = "ok" ]; then
      regressed=$((regressed+1)); echo "REGRESSION $n used to compile and now DECLINES"
    fi
  fi
done
echo "decline-shapes: $compiled compiled, $declined declined, $wrong WRONG-ANSWER, $progressed progressed, $regressed regressed"
[ "$wrong" -eq 0 ] && [ "$regressed" -eq 0 ]
