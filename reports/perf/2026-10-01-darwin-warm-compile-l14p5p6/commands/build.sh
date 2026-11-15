#!/bin/bash
# build.sh NAME: build the rustc bridge backend and the release CLI of
# $L14_CHECKOUT with the Trust package $TRUST_PKG (targo --unverified through
# scripts/trust_cargo.sh: no proof claim for the build) and copy them to
# $L14_WORK/bin/NAME.dylib and $L14_WORK/bin/NAME-cli. Copy each side out
# before building the other: the targets share one target directory.
set -u
export PATH="$HOME/.cargo/bin:$HOME/Library/Application Support/aterm/pkg/bin:/opt/homebrew/bin:$PATH" ATERM_REROUTE_QUIET=1 CARGO_BUILD_JOBS=3 CARGO_INCREMENTAL=0
PKG="${TRUST_PKG:?}"
W="${L14_CHECKOUT:?}"
S="${L14_WORK:?}"
name="$1"
cd "$W/crates/rustc-codegen-trust-cg" || exit 9
date -u +%FT%TZ; uptime
CARGO_TARGET_DIR="$W/crates/rustc-codegen-trust-cg/target-bridge" RUSTC="$PKG/bin/trustc" TRUST_TARGO="$PKG/bin/targo" \
  ../../scripts/trust_cargo.sh build --release --locked || exit $?
cp target-bridge/release/librustc_codegen_trust_cg.dylib "$S/bin/$name.dylib"
if [ "${2:-}" != "nocli" ]; then
cd "$W" || exit 9
scripts/trust_cargo.sh build --release --locked -p trust-cg-cli --bin trust-cg || exit $?
cp target/release/trust-cg "$S/bin/$name-cli"
fi
date -u +%FT%TZ; uptime
shasum -a 256 "$S/bin/$name.dylib" "$S/bin/$name-cli" 2>/dev/null
