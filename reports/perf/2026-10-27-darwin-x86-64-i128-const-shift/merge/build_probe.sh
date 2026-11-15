#!/bin/zsh
# OD-215 lane merged with origin/main: build slice 23's LOCAL x86 body probe (the copy of
# s23-fix/probe/x86_body_probe.rs beside this script, never committed) from wt-i128sh as it stands,
# through ../run.sh (build-slot, t011 targo --unverified, -j2); the example is copied in for the
# build and removed after. usage: build_probe.sh <tag>
TAG=${1:?tag}; W=$HOME/tcg-scratch/wt-i128sh; M=$HOME/tcg-scratch/i128sh-m1
cp $M/probe/x86_body_probe.rs $W/crates/trust-cg-verify/examples/x86_body_probe.rs
$M/run.sh build -p trust-cg-verify --example x86_body_probe -j2 > $M/logs/probe_build_$TAG.log 2>&1
RC=$?
rm -f $W/crates/trust-cg-verify/examples/x86_body_probe.rs
grep -E "^error|could not compile|Finished" $M/logs/probe_build_$TAG.log | tail -5
[ $RC = 0 ] && cp $HOME/tcg-scratch/stage1-targets/wt-i128sh/debug/examples/x86_body_probe $M/probe/x86_body_probe_$TAG && shasum -a 256 $M/probe/x86_body_probe_$TAG
echo "PROBE-BUILD-DONE rc=$RC"
