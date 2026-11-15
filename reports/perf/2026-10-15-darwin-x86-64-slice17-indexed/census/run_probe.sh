#!/bin/zsh
# Slice 17: the x86 body probe (`probe/x86_body_probe.rs` of the slice-16
# report, copied into `crates/trust-cg-verify/examples/` and built LOCAL ONLY,
# never committed) over a core dump, restricted to a names file, writing each
# built theorem's query (or parts). Niced, one thread, no AY.
# usage: run_probe.sh <probe binary> <dump dir> <names file> <out dir>
# RESPELL=1 (the default) re-spells slice 9's older dump for the pinned
# adapter; RESPELL=0 for a dump of a current bridge.
P=${1:?probe}; IR=${2:?dump dir}; NAMES=${3:?names}; OUT=${4:?out dir}
mkdir -p $OUT
export RAYON_NUM_THREADS=1 S16_ONLY_NAMES=1 RUST_MIN_STACK=67108864
if [[ ${RESPELL:-1} == 1 ]]; then export S16_RESPELL=1; fi
date
nice -n 19 $P --cf $IR $OUT/cf.tsv $OUT/smt2 $NAMES 2> $OUT/cf.err
echo "probe rc=$? $(date)"
