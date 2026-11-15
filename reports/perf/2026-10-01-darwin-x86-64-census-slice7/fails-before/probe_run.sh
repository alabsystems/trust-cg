#!/bin/zsh
# usage: run.sh <dylib> <src.rs> <outdir> [opt]
D="${1:?dylib}"; SRC="${2:?src}"; OUT="${3:?out}"; OPT="${4:-0}"
mkdir -p "$OUT"
export RUSTC_BOOTSTRAP=1 MACOSX_DEPLOYMENT_TARGET=13.0
trust/build/x86_64-apple-darwin/stage1/bin/trustc --edition=2021 -Ztrust-verify=off \
  --target x86_64-apple-darwin -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1 \
  -Copt-level=$OPT --crate-type rlib --crate-name callee -Zcodegen-backend="$D" \
  "-Ztrust-ir-cg-args=x86-body-trace dump-trust-ir=$OUT/ir" \
  --out-dir "$OUT" "$SRC" 2>&1 | grep -v '^rustc_codegen_trust_cg: emitted' | grep -v '^note' | cut -c1-400
ls "$OUT/ir"
