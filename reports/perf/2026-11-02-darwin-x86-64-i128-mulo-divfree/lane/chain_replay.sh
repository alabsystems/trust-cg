#!/bin/zsh
# OD-224 lane: offline replays on AY 13556 + Clean 5f09e36c (the t011 overlay's pair), one solver at
# a time (probe_run.py's gate), each function's replays one build-slot hold. (1) EVERY query of the
# changed functions in the new form (stage/new): each unit exact (whole or part), its OD-206
# generalization, each OD-197 claim exact and generalized, and a paired theorem's arbiter; (2) the
# production route (measure_mulo.py: unit exact, then its generalization, then claim by claim) on
# stage/new and on stage/old (= main's adapter).
M=$HOME/tcg-scratch/mulo-run; R=$M/replay
export BUILD_SLOT_MEM_GB=6
step() { echo "$(date +%H:%M:%S) $*" >> $R/chain_replay.txt; }
step START load=$(sysctl -n vm.loadavg)
while IFS=$'\t' read -r h name parts; do
  while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
  build-slot -- nice -n 19 python3 $R/replay_all.py new $M/stage/new/q $h > $R/all_new_$h.tsv 2> $R/all_new_$h.err
  step "all-routes $h ${name##*4core} rc=$? queries=$(wc -l < $R/all_new_$h.tsv | tr -d ' ') certified=$(grep -c '	certified	' $R/all_new_$h.tsv)"
done < $M/stage/new/q/index.tsv
for L in new old; do
  while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
  build-slot -- nice -n 19 python3 $R/measure_mulo.py ${L}_p4 $M/stage/$L > $R/route_${L}_p4.md 2> $R/route_${L}_p4.err
  step "route $L rc=$? $(tail -1 $R/route_${L}_p4.md)"
done
step CHAIN-REPLAY-DONE
