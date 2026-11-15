#!/bin/zsh
# OD-224 lane: start one run.sh job in the background, its log at logs/<tag>.log and its PID (run.sh
# execs build-slot, so the PID is the job's) at logs/<tag>.pid. usage: job.sh <tag> <run.sh args...>
M=$HOME/tcg-scratch/mulo-run; TAG=${1:?tag}; shift
nohup $M/run.sh "$@" > $M/logs/$TAG.log 2>&1 &
echo $! > $M/logs/$TAG.pid; echo "job $TAG pid $!"
