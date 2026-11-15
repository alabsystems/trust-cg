#!/bin/zsh
# Slice 23: the probe's --cf mode over a core dump, restricted to the names file's functions
# (S16_ONLY_NAMES), writing every theorem/part query, every unit's OD-197 claim split
# (S22_CLAIMS=1) and every unit's and claim's OD-206 generalization (S23_GENERAL=1).
# Niced, one thread, no AY. usage: run_probe.sh <probe binary> <dump dir> <names file> <out dir>
P=${1:?probe}; IR=${2:?dump dir}; NAMES=${3:?names}; OUT=${4:?out dir}
export RAYON_NUM_THREADS=1 S16_ONLY_NAMES=1 S22_CLAIMS=1 S23_GENERAL=1 RUST_MIN_STACK=67108864
mkdir -p "$OUT"; rm -rf "${OUT:?}/q"
nice -n 19 "$P" --cf $IR "$OUT/roots.tsv" "$OUT/q" $NAMES 2> "$OUT/roots.err"
echo "probe rc=$?"
