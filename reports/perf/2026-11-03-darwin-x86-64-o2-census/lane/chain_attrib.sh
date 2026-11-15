#!/bin/zsh
# O2 attribution censuses from the knob lane's bridge (~/tcg-scratch/runs/knobs.dylib, built
# from ~/tcg-scratch/wt-knobs, which its embedded drat-trim path names: keep that worktree).
# Each census disables passes through the tracked opt-outs; compare with the plain O2 census
# o2-7ee0 (same code apart from the knobs).
D=$HOME/tcg-scratch/runs/knobs.dylib
[ -f "$D" ] || { echo "no knobs.dylib"; exit 3; }
C=~/tcg-scratch/census_t011_dylib.sh
echo "== A-plain (knob dylib, no knob: must match o2-7ee0)"; $C $D o2k-plain 2
echo "== A-BM";  $C $D o2k-nbm 2 no-x86-block-merge
echo "== A-ROT"; $C $D o2k-nrot 2 no-x86-loop-rotate
echo "== A-IFC"; $C $D o2k-nifc 2 no-x86-ifconvert no-x86-cmov-swap
echo "== A-ALL"; $C $D o2k-nall 2 no-x86-block-merge no-x86-loop-rotate no-x86-ifconvert no-x86-cmov-swap no-x86-licm-loads no-x86-rmw-fuse no-x86-sroa
echo ATTRIB-DONE
