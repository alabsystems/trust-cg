#!/bin/bash
# One proofs-on bridge compile of a corpus program (diagnostic probe, not a
# measurement): the 2026-09-28 campaign's probe.sh with the checkout, output
# directory and package passed in instead of fixed.
#
# Usage: probe.sh <checkout> <out-dir> <trust-package> [program] [extra trustc args...]
set -u
WT="$1"
P="$2"
PKG="$3"
PROG="${4:-p3_gcd}"
shift 4 2>/dev/null || shift $#
export PATH="$HOME/.cargo/bin:/opt/homebrew/bin:$PATH" MACOSX_DEPLOYMENT_TARGET=13.0
mkdir -p "$P/probe"
cd "$WT" || exit 9
T0=$(python3 -c 'import time; print(time.time())')
"$PKG/bin/trustc" -Ztrust-verify=off \
  "-Zcodegen-backend=$WT/crates/rustc-codegen-trust-cg/target-bridge/release/librustc_codegen_trust_cg.dylib" \
  "$@" --edition=2021 --crate-type bin --target aarch64-apple-darwin -Cpanic=abort -Copt-level=3 \
  -o "$P/probe/$PROG" "benchmarks/beat-llvm/progs/$PROG.rs" > "$P/probe/$PROG${PROBE_TAG:-}.log" 2>&1
rc=$?
T1=$(python3 -c 'import time; print(time.time())')
echo "compile rc=$rc secs=$(python3 -c "print(round($T1-$T0,2))")"
tail -3 "$P/probe/$PROG${PROBE_TAG:-}.log"
if [ "$rc" = 0 ]; then
  "$P/probe/$PROG"; echo "program exit=$?"
fi
