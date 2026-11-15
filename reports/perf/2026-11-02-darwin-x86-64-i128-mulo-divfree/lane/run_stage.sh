#!/bin/zsh
# OD-224 lane: the probe over the functions whose theorems the division-free check changes
# (names.txt, from the whole-core comparison), writing each theorem's units, their OD-197 claim
# splits and their OD-206 generalizations (and a paired theorem's arbiter), in the new form and in
# the division form (old = main's adapter). Through build-slot. usage: run_stage.sh <probe> <dump dir>
P=${1:?probe}; IR=${2:?dump dir}; M=$HOME/tcg-scratch/mulo-run; S=$HOME/tcg-scratch/s23-run
export BUILD_SLOT_MEM_GB=6
build-slot -- env MULO_DIVISION_FORM=0 zsh $S/probe/run_probe.sh $P $IR $M/stage/names.txt $M/stage/new
build-slot -- env MULO_DIVISION_FORM=1 zsh $S/probe/run_probe.sh $P $IR $M/stage/names.txt $M/stage/old
echo STAGE-DONE
