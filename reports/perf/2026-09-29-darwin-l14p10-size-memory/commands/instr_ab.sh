#!/bin/bash
# instr_ab.sh <reps> <src>...: instructions retired and peak RSS of the bridge compile
# (no-proof-certs), baseline vs candidate backend, via /usr/bin/time -l.
S=$SCRATCH/l14p10
R="$1"; shift
for SRC in "$@"; do
  for pair in "baseline=$S/baseline.dylib" "candidate=$S/after.dylib"; do
    label="${pair%%=*}"; dylib="${pair#*=}"
    "$S/m" "$(basename "$SRC" .rs) $label" "$R" "$S/tc" "-Zcodegen-backend=$dylib" -Ztrust-ir-cg-args=no-proof-certs \
      -Ztrust-verify=off --edition=2021 --crate-type bin --target aarch64-apple-darwin -Cpanic=abort -Copt-level=3 \
      -o "$S/vm/instr_bin" "$SRC"
  done
done
