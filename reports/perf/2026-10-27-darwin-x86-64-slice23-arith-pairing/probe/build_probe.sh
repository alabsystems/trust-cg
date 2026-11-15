#!/bin/zsh
# Slice 23: build the LOCAL x86 body probe (slice 22's probe plus an OD-206 generalization writer,
# S23_GENERAL=1) from the wt-s23 worktree as it stands; the example is copied in for the build
# and removed after (never committed). targo --unverified via run.sh (no proof claim), -j2.
# usage: build_probe.sh <tag>
TAG=${1:?tag}; W=$HOME/tcg-scratch/wt-s23; S=$HOME/tcg-scratch/s23-run
cp $S/probe/x86_body_probe.rs $W/crates/trust-cg-verify/examples/x86_body_probe.rs
$S/run.sh build -p trust-cg-verify --example x86_body_probe -j2 > $S/logs/probe_build_$TAG.log 2>&1
RC=$?
rm -f $W/crates/trust-cg-verify/examples/x86_body_probe.rs
grep -E "^error|could not compile|Finished" $S/logs/probe_build_$TAG.log | tail -5
[ $RC = 0 ] && cp $HOME/tcg-scratch/stage1-targets/wt-s23/debug/examples/x86_body_probe $S/probe/x86_body_probe_$TAG && shasum -a 256 $S/probe/x86_body_probe_$TAG
echo "PROBE-BUILD-DONE rc=$RC"
