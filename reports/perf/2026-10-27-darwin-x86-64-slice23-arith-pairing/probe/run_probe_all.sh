#!/bin/zsh
# Slice 23: the probe over EVERY function of a core dump (no names file), writing every built
# theorem's queries (no claim split, no generalization). Niced, one thread, no AY.
# usage: run_probe_all.sh <probe binary> <dump dir> <out dir>
P=${1:?probe}; IR=${2:?dump dir}; OUT=${3:?out dir}
mkdir -p "$OUT"; rm -rf "${OUT:?}/smt2" "$OUT/cf.tsv" "$OUT/cf.err"
export RAYON_NUM_THREADS=1 RUST_MIN_STACK=67108864
date
nice -n 19 $P --cf $IR $OUT/cf.tsv $OUT/smt2 2> $OUT/cf.err
echo "probe rc=$? $(date)"
