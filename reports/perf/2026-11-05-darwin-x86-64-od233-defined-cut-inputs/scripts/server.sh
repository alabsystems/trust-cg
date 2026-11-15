#!/bin/bash
# Run inside ONE build-slot hold: execute each job file dropped into
# ~/tcg-scratch/od233-run/queue (one at a time, oldest first), logging to
# logs/<name>.log (ending "== JOB-EXIT=<rc>"); exit after 8 idle minutes so the
# slot is not held idle.
Q=$HOME/tcg-scratch/od233-run/queue
LOGS=$HOME/tcg-scratch/od233-run/logs
idle=0
echo "server up $(date +%H:%M:%S)"
while true; do
  job=$(ls -tr $Q/*.sh 2>/dev/null | grep -v '/running-\|/done-' | head -1)
  if [ -n "$job" ]; then
    name=$(basename "$job" .sh)
    mv "$job" "$Q/running-$name.sh"
    echo "job $name start $(date +%H:%M:%S)"
    bash "$Q/running-$name.sh" > "$LOGS/$name.log" 2>&1
    rc=$?
    echo "== JOB-EXIT=$rc $(date +%H:%M:%S)" >> "$LOGS/$name.log"
    mv "$Q/running-$name.sh" "$Q/done-$name.sh"
    echo "job $name exit $rc $(date +%H:%M:%S)"
    idle=0
  else
    sleep 5
    idle=$((idle + 5))
    if [ $idle -ge 480 ]; then echo "server idle, exiting $(date +%H:%M:%S)"; break; fi
  fi
done
