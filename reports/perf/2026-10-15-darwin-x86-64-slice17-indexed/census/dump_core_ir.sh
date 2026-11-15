#!/bin/zsh
# Slice 17 (from slice 16's): a fresh trust-ir dump of library/core from a census bridge,
# without proofs: the compile is stopped once the main CGU's module is written (the dump
# precedes codegen).
# AY RUNS: before the main CGU the bridge compiles, and proves, the small per-item
# modules (a resident `ay --incremental`, one-shot `ay -smt2` queries and Clean checks;
# measured by the slice-20 design on 2026-10-20, and so even with `no-proof-certs`), so
# a dump is a solver run for this host's one-solver rule (an earlier text said "No AY runs").
# usage: dump_core_ir.sh <bridge dylib> <out dir> <tag>
setopt NULL_GLOB
unset CARGO_TARGET_DIR
DYLIB=${1:?bridge dylib}; OUT=${2:?out dir}; TAG=${3:?tag}
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay12713
mkdir -p $OUT
RUSTC_BOOTSTRAP=1 nice -n 19 python3 trust/scripts/trust_ir_cg_census.py \
  --trustc $OV/bin/trustc --crate core \
  --out-dir $HOME/tcg-scratch/runs/$TAG-dump-census --backend $DYLIB \
  --opt-level 0 --panic abort \
  --extra-flag=-Ztrust-verify=off --extra-flag=-Ztrust-ir-cg-args=dump-trust-ir=$OUT \
  --timeout 7200 > $HOME/tcg-scratch/runs/$TAG-dump-census.out 2>&1 &
PY=$!
# Wait for the big CGU's module, then for its size to settle, then stop the compile.
until [ -n "$(echo $OUT/*cgu.0.rcgu.trust_irbin)" ] || ! kill -0 $PY 2>/dev/null; do sleep 10; done
prev=-1
while kill -0 $PY 2>/dev/null; do
  size=$(stat -f %z $OUT/*cgu.0.rcgu.trust_irbin 2>/dev/null | head -1)
  [ "$size" = "$prev" ] && [ -n "$size" ] && break
  prev=$size; sleep 20
done
pkill -f "[t]rust_ir_cg_census.py --trustc .*$TAG-dump-census"
pkill -f "[t]rustc .*dump-trust-ir=$OUT"
echo "DUMP-DONE $(date +%H:%M) $(ls $OUT | wc -l) files"
