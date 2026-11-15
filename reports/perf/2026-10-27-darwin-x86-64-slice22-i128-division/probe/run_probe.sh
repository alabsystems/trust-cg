#!/bin/zsh
# Slice 22: the probe's --cf mode over the FRESH core dump (core-ir-s22, the s21 census bridge
# 87407a8d…), restricted to the 14 class roots (S16_ONLY_NAMES), writing every theorem/part
# query and (S22_CLAIMS=1) every unit's OD-197 claim split. Niced, one thread, no AY.
# usage: run_probe.sh <probe binary> <out dir>
P=${1:?probe}; OUT=${2:?out dir}
IR=$HOME/tcg-scratch/runs/core-ir-s22
NAMES=$HOME/tcg-scratch/s22-run/probe/names14.txt
export RAYON_NUM_THREADS=1 S16_ONLY_NAMES=1 S22_CLAIMS=1 RUST_MIN_STACK=67108864
mkdir -p "$OUT"; rm -rf "${OUT:?}/q"
nice -n 19 "$P" --cf $IR "$OUT/roots14.tsv" "$OUT/q" $NAMES 2> "$OUT/roots14.err"
echo "probe rc=$?"
