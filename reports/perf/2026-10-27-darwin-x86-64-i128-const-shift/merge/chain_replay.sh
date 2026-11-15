#!/bin/zsh
# OD-215 lane merged with origin/main: offline replays on AY 13556 + Clean 5f09e36c (the t011
# overlay's pair), one solver at a time (probe_run.py's gate), each function's replays one
# build-slot hold. (1) EVERY query of the merged tree's 20 functions (stage/m1: the 17 the fold
# changes and slice 23's three roots): each unit exact (whole or part), its OD-206 generalization,
# each OD-197 claim exact and generalized, and a paired theorem's arbiter; (2) the production route
# (measure_m1.py: unit exact, then its generalization, then claim by claim) on stage/m1 and on
# stage/m1off (the fold off, = main), whose unchanged bytes are the cache's.
M=$HOME/tcg-scratch/i128sh-m1; R=$M/replay
export BUILD_SLOT_MEM_GB=6
step() { echo "$(date +%H:%M:%S) $*" >> $R/chain_replay.txt; }
step START load=$(sysctl -n vm.loadavg)
while IFS=$'\t' read -r h name parts; do
  while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
  build-slot -- nice -n 19 python3 $R/replay_all_m1.py m1 $M/stage/m1/q $h > $R/all_m1_$h.tsv 2> $R/all_m1_$h.err
  step "all-routes $h ${name##*4core} rc=$? queries=$(wc -l < $R/all_m1_$h.tsv | tr -d ' ') certified=$(grep -c '	certified	' $R/all_m1_$h.tsv)"
done < $M/stage/m1/q/index.tsv
for L in m1 m1off; do
  while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
  build-slot -- nice -n 19 python3 $R/measure_m1.py $L $M/stage/$L > $R/route_$L.md 2> $R/route_$L.err
  step "route $L rc=$? $(tail -1 $R/route_$L.md)"
done
step CHAIN-REPLAY-DONE
