#!/bin/zsh
# Slice 18: the x86 body probe (slice 16's `probe/x86_body_probe.rs`, built LOCAL ONLY in
# crates/trust-cg-verify/examples/, never committed) over a core trust-ir dump, restricted to a
# names file, writing each built theorem's query (or parts) as the live replay renders it.
# Niced, one thread, no AY. usage: run_probe.sh <probe binary> <dump dir> <names file> <out dir>
P=${1:?probe}; IR=${2:?dump dir}; NAMES=${3:?names}; OUT=${4:?out dir}
mkdir -p $OUT
export RAYON_NUM_THREADS=1 S16_ONLY_NAMES=1 RUST_MIN_STACK=67108864
date
nice -n 19 $P --cf $IR $OUT/cf.tsv $OUT/smt2 $NAMES 2> $OUT/cf.err
echo "probe rc=$? $(date)"
