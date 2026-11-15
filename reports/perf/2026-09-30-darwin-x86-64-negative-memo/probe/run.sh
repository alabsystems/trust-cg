#!/bin/zsh
# run.sh <dylib> <tag> [extra -Ztrust-ir-cg-args]
cd ~/tcg-scratch/fix-s5/probe
T=trust/build/x86_64-apple-darwin/stage1/bin/trustc
D="$1"; TAG="$2"; shift 2
mkdir -p out-$TAG
S=$(date +%s.%N 2>/dev/null || python3 -c 'import time;print(time.time())')
start=$(python3 -c 'import time;print(time.time())')
env -i PATH=/usr/bin:/bin HOME=$HOME RUSTC_BOOTSTRAP=1 MACOSX_DEPLOYMENT_TARGET=13.0 \
  $T --edition=2021 --crate-type lib --crate-name probe --emit=obj -Zcodegen-backend=$D \
  -Ccodegen-units=1 -Cpanic=abort -Copt-level=0 -Ztrust-verify=off --out-dir out-$TAG "$@" probe.rs > out-$TAG/stderr.log 2>&1
rc=$?
end=$(python3 -c 'import time;print(time.time())')
python3 -c "print('tag=$TAG rc=$rc wall=%.1fs' % ($end-$start))"
