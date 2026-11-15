#!/bin/bash
# Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
set -euo pipefail
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
task_tc=$HOME/.rustup/toolchains/1.97.1-aarch64-apple-darwin/bin
task_target=${CG_METADATA_TARGET_DIR:-/private/tmp/trust-cg-guard-regions-pin-20260908.ONRFiC/target}
task_prefix=${CG_METADATA_LOG_PREFIX:-final}
case "$task_prefix" in ''|*[!a-zA-Z0-9_-]*) exit 2 ;; esac
gate() {
  local task_weight=$1 task_label=$2
  shift 2
  local task_log="$task_root/reports/perf/2026-09-08-rewrite-metadata-pin/$task_prefix-$task_label.log"
  if test -e "$task_log"; then echo 'log exists; use a fresh prefix' >&2; exit 2; fi
  env -u RUSTC -u RUSTC_WRAPPER -u RUSTC_WORKSPACE_WRAPPER -u TRUST_IR_UPDATE_FIXTURES \
    RUSTFLAGS= RUSTDOCFLAGS= CARGO_ENCODED_RUSTFLAGS= \
    PATH="$task_tc:/usr/bin:/bin:/usr/sbin:/sbin" CARGO_TARGET_DIR="$task_target" \
    $HOME/clean/scripts/heavy_gate.sh run "$task_weight" "cg-rewrite-metadata-$task_label" -- \
    "$task_tc/cargo" "$@" 2>&1 | tee "$task_log"
}
if test "$#" -eq 0; then set -- lower native cache fuzz; fi
for task_selection in "$@"; do
  case "$task_selection" in
    lower) gate 4 lower test -p trust-cg-lower --all-features --locked -j2 -- --test-threads=1 --quiet ;;
    native) gate 5 native test -p trust-cg-codegen --test local_function_address_jit --test ty_callback_abi_call_clobber --locked -j2 -- --test-threads=1 --quiet ;;
    cache) gate 4 cache test -p trust-cg-codegen --lib artifact_cache --locked -j2 -- --test-threads=1 --quiet ;;
    fuzz) gate 5 fuzz check --manifest-path fuzz/Cargo.toml --all-features --bins --locked -j2 ;;
    *) exit 2 ;;
  esac
done
