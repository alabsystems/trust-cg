#!/bin/zsh
# One bounded wait for a job.sh job: until its PID exits (the writer is the job itself), at most
# <seconds>; prints the log's result lines. usage: waitjob.sh <seconds> <tag>
M=$HOME/tcg-scratch/mulo-run; END=$(( $(date +%s) + ${1:?secs} )); TAG=${2:?tag}
PID=$(cat $M/logs/$TAG.pid)
while [ $(date +%s) -lt $END ]; do
  kill -0 $PID 2>/dev/null || { echo "JOB-EXITED $TAG"; grep -E "^error|test result|panicked at|FAILED|^failures:" $M/logs/$TAG.log | head -40; exit 0; }
  sleep 15
done
echo "STILL-RUNNING $TAG: $(tail -1 $M/logs/$TAG.log | cut -c1-160)"; exit 1
