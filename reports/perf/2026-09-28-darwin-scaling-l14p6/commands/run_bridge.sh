#!/bin/bash
# Compile one scale_gate crate through the bridge (proofs off), -O3,
# aarch64-apple-darwin, under /usr/bin/time -l.
# Usage: run_bridge.sh <crate-name> <dylib> <outdir> [extra knobs, comma list]
set -u
export PATH="$HOME/.cargo/bin:/opt/homebrew/bin:$PATH" ATERM_REROUTE_QUIET=1
PKG="$HOME/Library/Application Support/aterm/pkg/store/trust/9192"
S=$SCRATCH/l14p6
NAME="$1"
DYLIB="$2"
OUT="$3"
EXTRA="${4:-}"
mkdir -p "$OUT"
KNOBS="no-proof-certs"
if [ -n "$EXTRA" ]; then KNOBS="$KNOBS ${EXTRA//,/ }"; fi
echo "load: $(sysctl -n vm.loadavg)" > "$OUT/$NAME.time"
/usr/bin/time -l "$PKG/bin/trustc" -Ztrust-verify=off "-Zcodegen-backend=$DYLIB" "-Ztrust-ir-cg-args=$KNOBS" \
  --edition=2021 --crate-type bin --target aarch64-apple-darwin -Cpanic=abort -Copt-level=3 \
  -C save-temps -o "$OUT/$NAME.bin" "$S/crates/$NAME.rs" 2>>"$OUT/$NAME.time"
rc=$?
echo "exit=$rc" >> "$OUT/$NAME.time"
exit $rc
