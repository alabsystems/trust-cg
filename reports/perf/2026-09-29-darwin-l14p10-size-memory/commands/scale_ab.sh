#!/bin/bash
# scale_ab.sh <N> <size> <label=dylib>...: compiler peak RSS on a scale-gate crate,
# LLVM -O2 and each bridge dylib (no-proof-certs), median of N.
S=$SCRATCH/l14p10
TC="$HOME/Library/Application Support/aterm/pkg/store/trust/9192/bin/trustc"
N="$1"; SIZE="$2"; shift 2
SRC="$S/scale/$SIZE.rs"
export MACOSX_DEPLOYMENT_TARGET=13.0
COMMON=(-Ztrust-verify=off --edition=2021 --crate-type bin --target aarch64-apple-darwin -Cpanic=abort)
python3 "$S/pm.py" "$N" "$SIZE llvm -O2" -- "$TC" "${COMMON[@]}" -Copt-level=2 -o "$S/vm/sc_l" "$SRC"
for pair in "$@"; do
  label="${pair%%=*}"; dylib="${pair#*=}"
  python3 "$S/pm.py" "$N" "$SIZE $label" -- "$TC" "-Zcodegen-backend=$dylib" -Ztrust-ir-cg-args=no-proof-certs "${COMMON[@]}" -Copt-level=3 -o "$S/vm/sc_b" "$SRC"
done
