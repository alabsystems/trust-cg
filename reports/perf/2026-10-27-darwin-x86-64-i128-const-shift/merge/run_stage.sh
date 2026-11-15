#!/bin/zsh
# OD-215 lane merged with origin/main: the probe over the 17 functions the fold changes and slice
# 23's three roots (names20.txt), writing each theorem's units, their OD-197 claim splits and their
# OD-206 generalizations (and the arbiter's theorem of a paired one), with the fold (m1) and without
# it (m1off: TCG_NO_X86_I128_CONST_SHIFT=1, = main). Through build-slot.
M=$HOME/tcg-scratch/i128sh-m1; S=$HOME/tcg-scratch/s23-run; IR=$HOME/tcg-scratch/runs/core-ir-s23
export BUILD_SLOT_MEM_GB=6
build-slot -- zsh $S/probe/run_probe.sh $M/probe/x86_body_probe_m1 $IR $M/stage/names20.txt $M/stage/m1
build-slot -- env TCG_NO_X86_I128_CONST_SHIFT=1 zsh $S/probe/run_probe.sh $M/probe/x86_body_probe_m1 $IR $M/stage/names20.txt $M/stage/m1off
echo STAGE-DONE
