#!/bin/zsh
# Slice-23 review fixes: build slice 23's LOCAL x86 body probe (s23-run/probe/x86_body_probe.rs,
# never committed) from the wt-s23 worktree as it stands, through s23-run/run.sh (build-slot,
# targo --unverified, -j2); the example is copied in for the build and removed after.
# usage: build_probe.sh <tag>
TAG=${1:?tag}; W=$HOME/tcg-scratch/wt-s23; S=$HOME/tcg-scratch/s23-run; F=$HOME/tcg-scratch/s23-fix
cp ${PROBE_SRC:-$S/probe/x86_body_probe.rs} $W/crates/trust-cg-verify/examples/x86_body_probe.rs
${RUN:-$S/run.sh} build -p trust-cg-verify --example x86_body_probe -j2 > $F/logs/probe_build_$TAG.log 2>&1
RC=$?
rm -f $W/crates/trust-cg-verify/examples/x86_body_probe.rs
grep -E "^error|could not compile|Finished" $F/logs/probe_build_$TAG.log | tail -5
[ $RC = 0 ] && cp $HOME/tcg-scratch/stage1-targets/wt-s23/debug/examples/x86_body_probe $F/probe/x86_body_probe_$TAG && shasum -a 256 $F/probe/x86_body_probe_$TAG
echo "PROBE-BUILD-DONE rc=$RC"
