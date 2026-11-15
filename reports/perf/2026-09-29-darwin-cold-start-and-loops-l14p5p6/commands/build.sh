#!/bin/bash
# Build the rustc bridge backend and the release CLI of one checkout with the
# Trust package (explicit unverified lane; no proof claim for the build).
#
#   L14_CHECKOUT  the repository checkout to build
#   TRUST_PKG     the Trust package root (bin/trustc, bin/targo)
#
# The backend lands in $L14_CHECKOUT/crates/rustc-codegen-trust-cg/target-bridge
# /release/librustc_codegen_trust_cg.dylib, the CLI in
# $L14_CHECKOUT/target/release/trust-cg. Copy both out before building the
# other side: the report compares a copy of each.
set -u
: "${L14_CHECKOUT:?}" "${TRUST_PKG:?}"
export ATERM_REROUTE_QUIET=1 CARGO_BUILD_JOBS=3 CARGO_INCREMENTAL=0
cd "$L14_CHECKOUT/crates/rustc-codegen-trust-cg" || exit 9
date -u +%FT%TZ; uptime
CARGO_TARGET_DIR="$L14_CHECKOUT/crates/rustc-codegen-trust-cg/target-bridge" \
  RUSTC="$TRUST_PKG/bin/trustc" TRUST_TARGO="$TRUST_PKG/bin/targo" \
  /usr/bin/time -l ../../scripts/trust_cargo.sh build --release --locked || exit $?
cd "$L14_CHECKOUT" || exit 9
/usr/bin/time -l scripts/trust_cargo.sh build --release --locked -p trust-cg-cli --bin trust-cg
rc=$?
date -u +%FT%TZ; uptime
exit $rc
