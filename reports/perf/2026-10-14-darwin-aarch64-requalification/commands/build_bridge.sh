#!/bin/bash
set -u
WT="$1"
PKG="$2"
export PATH="$HOME/.cargo/bin:$HOME/Library/Application Support/aterm/pkg/bin:/opt/homebrew/bin:$PATH"
export ATERM_REROUTE_QUIET=1 CARGO_BUILD_JOBS=3 CARGO_INCREMENTAL=0
cd "$WT/crates/rustc-codegen-trust-cg" || exit 9
date -u +%FT%TZ
uptime
export CARGO_TARGET_DIR=target-bridge RUSTC="$PKG/bin/trustc" TRUST_TARGO="$PKG/bin/targo"
/usr/bin/time -l ../../scripts/trust_cargo.sh build --release --locked
rc=$?
date -u +%FT%TZ
uptime
echo "exit=$rc"
exit $rc
