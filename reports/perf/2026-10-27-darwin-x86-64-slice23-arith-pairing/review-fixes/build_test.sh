#!/bin/zsh
# Slice-23 review fixes: build the trust-cg-verify library tests in wt-s23 (through s23-run/run.sh:
# build-slot, the AY 13556 overlay, targo --unverified) and copy the binary aside.
# usage: build_test.sh <tag>
TAG=${1:?tag}; S=$HOME/tcg-scratch/s23-run; F=$HOME/tcg-scratch/s23-fix
rm -rf $HOME/tcg-scratch/stage1-targets/wt-s23/debug/incremental
${RUN:-$S/run.sh} test -p trust-cg-verify --lib --no-run -j2 > $F/logs/build_$TAG.log 2>&1
grep -qE '^ *Finished' $F/logs/build_$TAG.log || { echo "BUILD FAILED $TAG"; grep -E '^(error|warning)' -A14 $F/logs/build_$TAG.log | head -150; exit 1; }
B=$(grep -o 'Executable unittests src/lib.rs ([^)]*)' $F/logs/build_$TAG.log | sed 's/.*(\(.*\))/\1/')
cp "$B" $F/testbin_$TAG && echo "testbin_$TAG <- $B"
