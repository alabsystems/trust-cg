#!/bin/zsh
# Build the trust-cg-verify library tests in wt-s22 and copy the binary the build names (the
# deps hash moves with the dependency graph: never copy a fixed name). usage: build_test.sh <tag>
TAG=${1:?tag}; S=$HOME/tcg-scratch/s22-run
rm -rf $HOME/tcg-scratch/stage1-targets/wt-s22/debug/incremental
$S/run.sh test -p trust-cg-verify --lib --no-run -j2 > $S/logs/build_$TAG.log 2>&1
grep -qE '^ *Finished' $S/logs/build_$TAG.log || { echo "BUILD FAILED $TAG"; grep -E '^error' -A12 $S/logs/build_$TAG.log | head -60; exit 1; }
B=$(grep -o 'Executable unittests src/lib.rs ([^)]*)' $S/logs/build_$TAG.log | sed 's/.*(\(.*\))/\1/')
cp "$B" $S/testbin_$TAG && echo "testbin_$TAG <- $B"
