#!/bin/zsh
# Second O2 attribution chain (knobs.dylib = main 0c8f408c8's code; built in ~/tcg-scratch/wt-knobs):
#  A-B0: -Copt-level=2 with the backend at O0 (MIR-O2 shapes alone)
#  A-B1: -Copt-level=2 with the backend at O1
#  A-MAX: O2 with every pass knob that exists off (the seven plus vectorize, strength reduce, slot forward,
#         BCE, xorshift demanded bits, partial and const-address unroll)
D=$HOME/tcg-scratch/runs/knobs.dylib
C=~/tcg-scratch/census_t011_dylib.sh
echo "== A-B0"; $C $D o2k-b0 2 opt-level=0
echo "== A-B1"; $C $D o2k-b1 2 opt-level=1
echo "== A-MAX"; $C $D o2k-nmax 2 no-x86-block-merge no-x86-loop-rotate no-x86-ifconvert no-x86-cmov-swap no-x86-licm-loads no-x86-rmw-fuse no-x86-sroa no-x86-vectorize no-x86-strength-reduce no-x86-slot-forward no-x86-bce no-x86-xorshift-demanded-bits no-partial-unroll no-const-addr-unroll
echo ATTRIB2-DONE
