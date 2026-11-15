#!/bin/zsh
# Compile each reproducer crate of `crates/` through a release bridge (the
# census's lane: the x86-stage1-ay13556 overlay trustc, AY 13556 + Clean
# 5f09e36c, O0, panic=abort, proofs required) with the x86-64 body trace, and
# record every trace line, the objects' defined symbols and the codegen-unit
# placement. usage: run_crates.sh <bridge dylib> <out dir>
# Run it under build-slot. The trace line of a function names its body
# theorem's outcome: `bound rows=N replay=Valid` is Formal credit for its rows;
# a refusal names its reason (OD-216's names the routine and who defines it).
D=${1:?dylib}; OUT=${2:?out dir}
HERE=${0:A:h}
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556
mkdir -p $OUT
: > $OUT/summary.txt
shasum -a 256 $D | sed 's/^/bridge sha256 /' >> $OUT/summary.txt
# CASES (crate:codegen-units ...) overrides the list.
for CASE in ${=CASES:-div_split:16 div_split:1 div_declared:16 div_declared:1 copy_split:16 copy_split:1 copy_declared:16 copy_declared:1 copy_self:1}; do
  CRATE=${CASE%%:*}; CGU=${CASE##*:}; TAG=${CRATE}_cgu$CGU
  rm -rf $OUT/$TAG; mkdir -p $OUT/$TAG
  while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
  RUSTC_BOOTSTRAP=1 $OV/bin/trustc --edition 2024 --crate-type lib --crate-name $CRATE \
    --emit=obj -Zcodegen-backend=$D -Ccodegen-units=$CGU -Cpanic=abort -Copt-level=0 \
    -Ztrust-verify=off -Ztrust-ir-cg-args=x86-body-trace -Zprint-mono-items=yes \
    --out-dir $OUT/$TAG $HERE/crates/$CRATE.rs > $OUT/$TAG/stdout.log 2> $OUT/$TAG/stderr.log
  RC=$?
  {
    echo "== $TAG exit=$RC"
    grep -h 'MONO_ITEM' $OUT/$TAG/stdout.log | grep -E 'fn (div|copy_bytes|memcpy|memmove|__udivti3|core::ptr::copy)' | sed 's/^/  /'
    grep -ah '\[TCG-X86-BODY-TRACE\]' $OUT/$TAG/stderr.log | sed 's/^/  /'
    for o in $OUT/$TAG/*.o(N); do nm -U $o | awk '{print "  defines " $NF}'; done | sort -u
    grep -ah '^error' $OUT/$TAG/stderr.log | head -5 | sed 's/^/  /'
  } >> $OUT/summary.txt
done
echo RUN-CRATES-DONE >> $OUT/summary.txt
