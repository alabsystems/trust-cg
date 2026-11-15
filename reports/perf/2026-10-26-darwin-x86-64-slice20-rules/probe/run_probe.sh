#!/bin/zsh
# The slice-20 branch's owner through the design's probe (--cf) over the census bridge's core
# dump (`runs/core-ir-s20`), restricted to census-ay13556's 106 failed roots (S16_ONLY_NAMES:
# every other function a declaration). No lift is set (S20_DIV128 unset, the selector's own
# binary search): the rules are this branch's. Niced, one thread, no AY.
# usage: run_probe.sh <label>
D=$HOME/tcg-scratch/s20-impl/probe
P=$HOME/tcg-scratch/s20-impl/bin/x86_body_probe_s20impl
IR=$HOME/tcg-scratch/runs/core-ir-s20
L=${1:?label}
export RAYON_NUM_THREADS=1 S16_ONLY_NAMES=1 RUST_MIN_STACK=67108864
date
rm -rf "${D:?}/${L:?}.smt2"
nice -n 19 $P --cf $IR $D/$L.tsv $D/$L.smt2 $HOME/tcg-scratch/s20-design/data/names_roots.txt 2> $D/$L.err
echo "probe $L rc=$? $(date)"
