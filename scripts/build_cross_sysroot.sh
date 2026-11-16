#!/usr/bin/env bash
# scripts/build_cross_sysroot.sh — a cross-target std sysroot for the rustc
# bridge's object-emission parity tests on an x86-64 Linux host.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# Usage: scripts/build_cross_sysroot.sh <out-sysroot> [toolchain-bin-dir]
#
# Builds `std` (with `panic_abort`) for aarch64-unknown-linux-gnu,
# aarch64-apple-darwin and wasm32-unknown-unknown with the toolchain's own
# `cargo -Zbuild-std` from that toolchain's `rust-src` component, OFFLINE: the
# crates.io dependencies of `library/Cargo.lock` must already be in the Cargo
# registry cache. Each target's newest rlib per crate is copied to
# `<out>/lib/rustlib/<target>/lib`. Trust verification is off for these
# builds (a wrapper adds `-Ztrust-verify=off` to every rustc call, build
# scripts included): the sysroot is test input for codegen tests, not a
# verified artifact. Final executables are not linked (no cross linker is
# needed or used; the dummy crate's link step is expected to fail for the
# native targets). Point SLICE_PARITY_CROSS_SYSROOT at the output for
# `tests/slice_parity_cross_targets.rs`.
set -euo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "usage: $0 <out-sysroot> [toolchain-bin-dir]" >&2
  exit 2
fi
out=$1
bin=${2:-$(dirname "$(command -v trustc)")}
for tool in trustc cargo; do
  if [[ ! -x "$bin/$tool" ]]; then
    echo "error: no $bin/$tool" >&2
    exit 2
  fi
done

work=$(mktemp -d)
trap 'rm -rf "${work:?}"' EXIT
mkdir -p "$work/dummy/src"
printf '[package]\nname = "dummy"\nversion = "0.1.0"\nedition = "2021"\n[profile.release]\npanic = "abort"\n' \
  >"$work/dummy/Cargo.toml"
echo 'fn main() { println!("x"); }' >"$work/dummy/src/main.rs"
printf '#!/bin/sh\nr="$1"; shift\nexec "$r" -Ztrust-verify=off "$@"\n' >"$work/wrap.sh"
chmod +x "$work/wrap.sh"

for target in aarch64-unknown-linux-gnu aarch64-apple-darwin wasm32-unknown-unknown; do
  (cd "$work/dummy" &&
    env -i PATH="$bin:/usr/bin:/bin" HOME="$HOME" RUSTC="$bin/trustc" \
      RUSTC_WRAPPER="$work/wrap.sh" __CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS=nightly \
      "$bin/cargo" build --offline --release -Zbuild-std=std,panic_abort --target "$target" \
      >"$work/$target.log" 2>&1) || true
  lib="$out/lib/rustlib/$target/lib"
  mkdir -p "$lib"
  for crate in "$work/dummy/target/$target/release/build"/*/; do
    newest=$(ls -t "$crate"*/out/*.rlib 2>/dev/null | head -1 || true)
    if [[ -n "$newest" ]]; then
      cp "$newest" "$lib/"
    fi
  done
  if ! ls "$lib"/libstd-*.rlib >/dev/null 2>&1; then
    echo "error: no std rlib for $target; see the build log:" >&2
    tail -20 "$work/$target.log" >&2
    exit 1
  fi
done
echo "$out"
