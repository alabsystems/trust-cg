#!/bin/zsh
# Slice 19: the local x86 body probe over census-ay13556's bridge's core trust-ir dump
# (runs/core-ir-s20, byte-identical main module to core-ir-s17), restricted to a names file,
# writing each built theorem's queries (or parts). Niced, one thread, no AY.
# usage: run_probe.sh <probe binary> <names file> <out dir>
P=${1:?probe}; NAMES=${2:?names}; OUT=${3:?out dir}
IR=$HOME/tcg-scratch/runs/core-ir-s20
rm -rf "${OUT:?}"; mkdir -p $OUT
export RAYON_NUM_THREADS=1 S16_ONLY_NAMES=1 RUST_MIN_STACK=67108864
date
nice -n 19 $P --cf $IR $OUT/cf.tsv $OUT/smt2 $NAMES 2> $OUT/cf.err
echo "probe rc=$? $(date)"
