#!/bin/zsh
# Build the trust-cg-verify library tests in wt-i128sh (run.sh: build-slot, t011 targo, -j2) and copy
# the binary aside. usage: build_test.sh <tag>
TAG=${1:?tag}; M=$HOME/tcg-scratch/i128sh-m1
rm -rf $HOME/tcg-scratch/stage1-targets/wt-i128sh/debug/incremental
$M/run.sh test -p trust-cg-verify --lib --no-run -j2 > $M/logs/build_$TAG.log 2>&1
grep -qE '^ *Finished' $M/logs/build_$TAG.log || { echo "BUILD FAILED $TAG"; grep -E '^(error|warning)' -A14 $M/logs/build_$TAG.log | head -150; exit 1; }
B=$(grep -o 'Executable unittests src/lib.rs ([^)]*)' $M/logs/build_$TAG.log | sed 's/.*(\(.*\))/\1/')
cp "$B" $M/testbin_$TAG && echo "testbin_$TAG <- $B"
