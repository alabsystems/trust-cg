#!/bin/zsh
# Slice 22: the probe over EVERY function of the fresh core dump (core-ir-s22; no names file),
# writing every built theorem's queries (no claim split). Niced, one thread, no AY.
# usage: run_probe_all.sh <probe binary> <out dir>
P=${1:?probe}; OUT=${2:?out dir}
IR=$HOME/tcg-scratch/runs/core-ir-s22
mkdir -p "$OUT"; rm -rf "$OUT/smt2" "$OUT/cf.tsv" "$OUT/cf.err"
export RAYON_NUM_THREADS=1 RUST_MIN_STACK=67108864
date
nice -n 19 $P --cf $IR $OUT/cf.tsv $OUT/smt2 2> $OUT/cf.err
echo "probe rc=$? $(date)"
