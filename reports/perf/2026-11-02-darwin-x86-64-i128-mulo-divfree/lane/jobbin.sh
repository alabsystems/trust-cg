#!/bin/zsh
# job.sh for runbin.sh. usage: jobbin.sh <tag> <binary> <test args...>
M=$HOME/tcg-scratch/mulo-run; TAG=${1:?tag}; shift
nohup $M/runbin.sh "$@" > $M/logs/$TAG.log 2>&1 &
echo $! > $M/logs/$TAG.pid; echo "job $TAG pid $!"
