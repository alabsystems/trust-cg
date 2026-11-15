#!/bin/zsh
# The slice-21 branch's owner through the slice-20 probe (`x86_body_probe.rs`, which adds an
# FP-ABSTRACT mark to a built theorem's verdict) in `--cf` mode over the census-s20 bridge's
# `core` trust-ir dump, restricted to the design's 12 roots (S16_ONLY_NAMES: every other function
# a declaration). Place the probe in `crates/trust-cg-verify/examples/` and build it with
# `scripts/trust_cargo.sh build -p trust-cg-verify --example x86_body_probe` first (never
# committed). Niced, one thread, no AY.
# usage: run_probe.sh <probe binary> <out dir>
P=${1:?probe}; OUT=${2:?out dir}
IR=$HOME/tcg-scratch/runs/core-ir-s20
NAMES=$HOME/tcg-scratch/s21-design/data/names12.txt
export RAYON_NUM_THREADS=1 S16_ONLY_NAMES=1 RUST_MIN_STACK=67108864
mkdir -p "$OUT"; rm -rf "${OUT:?}/roots12.smt2"
nice -n 19 "$P" --cf $IR "$OUT/roots12.tsv" "$OUT/roots12.smt2" $NAMES 2> "$OUT/roots12.err"
echo "probe rc=$?"
