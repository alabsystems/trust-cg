#!/bin/zsh
# The local probe over every function of census-ay13556's core trust-ir dump (no names file),
# writing every built theorem's queries. Niced, one thread, no AY.
# usage: run_probe_all.sh <probe binary> <out dir>
P=${1:?probe}; OUT=${2:?out dir}
IR=$HOME/tcg-scratch/runs/core-ir-s20
rm -rf "${OUT:?}"; mkdir -p $OUT
export RAYON_NUM_THREADS=1 RUST_MIN_STACK=67108864
date
nice -n 19 $P --cf $IR $OUT/cf.tsv $OUT/smt2 2> $OUT/cf.err
echo "probe rc=$? $(date)"
