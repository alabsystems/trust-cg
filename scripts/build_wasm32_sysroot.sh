#!/usr/bin/env bash
# scripts/build_wasm32_sysroot.sh — a wasm32-unknown-unknown sysroot for the
# rustc bridge's wasm32 lane and its execution differential.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# Usage: scripts/build_wasm32_sysroot.sh <trust-checkout> <out-sysroot> [trustc]
#
# Builds `core` and `compiler_builtins` for wasm32-unknown-unknown with the
# given compiler (default: `trustc` on PATH) from THAT compiler's own library
# sources: the commit named by `trustc -vV` is exported from <trust-checkout>,
# so the rlibs match the compiler's metadata format and lang items. Trust
# verification is off for these builds: the sysroot is test input for codegen
# differentials, not a verified artifact. Point WASM32_SYSROOT at the output.
set -euo pipefail

if [[ $# -lt 2 || $# -gt 3 ]]; then
  echo "usage: $0 <trust-checkout> <out-sysroot> [trustc]" >&2
  exit 2
fi
trust=$1
out=$2
trustc=${3:-$(command -v trustc || true)}
if [[ -z "$trustc" || ! -x "$trustc" ]]; then
  echo "error: no trustc (pass it as the third argument)" >&2
  exit 2
fi
rev=$("$trustc" -vV | sed -n 's/^commit-hash: //p')
if [[ -z "$rev" ]]; then
  echo "error: $trustc -vV names no commit-hash" >&2
  exit 2
fi

src=$(mktemp -d)
trap 'rm -rf "${src:?}"' EXIT
git -C "$trust" archive "$rev" \
  library/core library/compiler-builtins library/stdarch library/portable-simd |
  tar -x -C "$src"

lib="$out/lib/rustlib/wasm32-unknown-unknown/lib"
mkdir -p "$lib"
common=(--target wasm32-unknown-unknown -Ztrust-verify=off -Cpanic=abort -Copt-level=3
  -Zforce-unstable-if-unmarked -Cembed-bitcode=no)
RUSTC_BOOTSTRAP=1 "$trustc" --edition 2024 --crate-type rlib --crate-name core "${common[@]}" \
  "$src/library/core/src/lib.rs" -o "$lib/libcore.rlib"
RUSTC_BOOTSTRAP=1 "$trustc" --edition 2024 --crate-type rlib --crate-name compiler_builtins \
  "${common[@]}" --cfg 'feature="compiler-builtins"' --cfg 'feature="unmangled-names"' \
  --cfg 'feature="mem"' --extern core="$lib/libcore.rlib" \
  "$src/library/compiler-builtins/compiler-builtins/src/lib.rs" \
  -o "$lib/libcompiler_builtins.rlib"
echo "$out"
