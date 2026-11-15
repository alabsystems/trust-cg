#!/bin/zsh
# Slice 22 (a copy of slice 18's, on the AY 13556 overlay): a trust-ir dump of library/core from a census bridge (the bytes that bridge's
# census compiled), without proofs and without the census script: trustc runs with the bridge
# and `dump-trust-ir=`, and is stopped once the main CGU's module is written and its size has
# settled (the dump precedes codegen).
# AY RUNS: before the main CGU the bridge compiles, and proves, the small per-item
# modules (a resident `ay --incremental`, one-shot `ay -smt2` queries and Clean checks;
# measured by the slice-20 design on 2026-10-20, and so even with `no-proof-certs`), so
# a dump is a solver run for this host's one-solver rule (an earlier text said "No AY runs").
# usage: dump_core_ir.sh <bridge dylib> <out dir>
setopt NULL_GLOB
unset CARGO_TARGET_DIR
DYLIB=${1:?bridge dylib}; OUT=${2:?out dir}
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556
mkdir -p $OUT $OUT.obj
RUSTC_BOOTSTRAP=1 nice -n 19 $OV/bin/trustc --edition 2024 --crate-type lib --crate-name core \
  --emit=obj -Zcodegen-backend=$DYLIB -Ccodegen-units=1 -Cpanic=abort -Copt-level=0 \
  -Ztrust-verify=off --out-dir $OUT.obj -Ztrust-ir-cg-args=dump-trust-ir=$OUT \
  $HOME/trust/library/core/src/lib.rs > $OUT.log 2>&1 &
PID=$!
until [ -n "$(echo $OUT/*cgu.0.rcgu.trust_irbin)" ] || ! kill -0 $PID 2>/dev/null; do sleep 10; done
prev=-1
while kill -0 $PID 2>/dev/null; do
  size=$(stat -f %z $OUT/*cgu.0.rcgu.trust_irbin 2>/dev/null | head -1)
  [ "$size" = "$prev" ] && [ -n "$size" ] && break
  prev=$size; sleep 20
done
kill $PID 2>/dev/null
echo "DUMP-DONE $(date +%H:%M) $(ls $OUT | wc -l) files"
