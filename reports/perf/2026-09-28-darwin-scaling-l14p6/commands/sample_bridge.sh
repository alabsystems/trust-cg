#!/bin/bash
# Start a bridge compile of one crate and sample its stacks with macOS
# `sample` after a delay.
# Usage: sample_bridge.sh <crate-name> <dylib> <outdir> <delay-s> <duration-s>
set -u
export PATH="$HOME/.cargo/bin:/opt/homebrew/bin:$PATH" ATERM_REROUTE_QUIET=1
PKG="$HOME/Library/Application Support/aterm/pkg/store/trust/9192"
S=$SCRATCH/l14p6
NAME="$1"
DYLIB="$2"
OUT="$3"
DELAY="$4"
DUR="$5"
mkdir -p "$OUT"
"$PKG/bin/trustc" -Ztrust-verify=off "-Zcodegen-backend=$DYLIB" "-Ztrust-ir-cg-args=no-proof-certs" \
  --edition=2021 --crate-type bin --target aarch64-apple-darwin -Cpanic=abort -Copt-level=3 \
  -o "$OUT/$NAME.bin" "$S/crates/$NAME.rs" 2>"$OUT/$NAME.stderr" &
PID=$!
sleep "$DELAY"
/usr/bin/sample "$PID" "$DUR" 1 -mayDie -file "$OUT/$NAME.sample.txt" >/dev/null 2>&1
wait "$PID"
echo "exit=$?"
