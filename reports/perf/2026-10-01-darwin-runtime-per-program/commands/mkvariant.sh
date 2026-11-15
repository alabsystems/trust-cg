#!/bin/bash
# Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
# mkvariant.sh <work-dir> <name> <source.rs> <lane=dylib|llvm>...
# Compiles <source.rs> as the harness does (-O3, panic=abort) into
# <work-dir>/<name>/<lane>/<name>, for bench.py.
set -e
export PATH="$HOME/.cargo/bin:$HOME/Library/Application Support/aterm/pkg/bin:/opt/homebrew/bin:$PATH" ATERM_REROUTE_QUIET=1 MACOSX_DEPLOYMENT_TARGET=13.0
work=$1; name=$2; src=$3; shift 3
for spec in "$@"; do
  lane=${spec%%=*}; dylib=${spec#*=}
  out=$work/$name/$lane; mkdir -p $out
  extra=()
  if [ "$dylib" != llvm ]; then extra=(-Zcodegen-backend=$dylib -Ztrust-ir-cg-args=no-proof-certs); fi
  (cd $out && trustc -Ztrust-verify=off "${extra[@]}" --edition=2021 --crate-type bin --target aarch64-apple-darwin -Cpanic=abort -Copt-level=3 -o $out/$name $src 2>&1 | grep -E "^error" -A3 || true)
  test -x $out/$name || { echo "compile failed: $name $lane"; exit 1; }
done
