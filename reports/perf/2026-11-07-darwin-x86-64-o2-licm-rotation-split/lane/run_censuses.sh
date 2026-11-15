#!/bin/zsh
# Runs the two single-knob O2 censuses one after the other, each through build-slot.
cd ~/tcg-scratch/s26-rebase || exit 2
echo "l queued $(date +%H:%M:%S)"
BUILD_SLOT_MEM_GB=6 build-slot -- ~/tcg-scratch/census_t011_dylib.sh ~/tcg-scratch/runs/o2-m301.dylib o2k-m301-l 2 no-x86-licm
echo "l rc=$? $(date +%H:%M:%S)"
echo "r queued $(date +%H:%M:%S)"
BUILD_SLOT_MEM_GB=6 build-slot -- ~/tcg-scratch/census_t011_dylib.sh ~/tcg-scratch/runs/o2-m301.dylib o2k-m301-r 2 no-x86-loop-rotate
echo "r rc=$? $(date +%H:%M:%S)"
echo ALL-DONE
