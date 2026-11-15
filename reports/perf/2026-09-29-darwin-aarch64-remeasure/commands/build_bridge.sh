#!/bin/bash
# Build the rustc bridge backend the harnesses load, with the Trust package's
# targo in its UNVERIFIED lane through scripts/trust_cargo.sh (no proof claim
# about the build). This is the 2026-09-28 campaign's build command
# (`cd crates/rustc-codegen-trust-cg && CARGO_TARGET_DIR=target-bridge
# RUSTC=<pkg>/bin/trustc <pkg>/bin/targo --unverified build --release --locked`)
# routed through the repository's Cargo wrapper, with the same package named
# explicitly (TRUST_TARGO, RUSTC).
#
# Usage: build_bridge.sh <checkout> <trust-package>
set -u
WT="$1"
PKG="$2"
export PATH="$HOME/.cargo/bin:/opt/homebrew/bin:$HOME/Library/Application Support/aterm/pkg/bin:$PATH"
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
