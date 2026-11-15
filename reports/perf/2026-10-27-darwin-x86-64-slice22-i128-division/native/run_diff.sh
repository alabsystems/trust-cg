#!/bin/zsh
# Slice 22 (OD-202): the native differential of the four 128-bit division routines the x86-64
# selector calls, against an independent bit-serial reference (diff_ti3.c), in both bindings:
# libSystem's (a `cc` link) and the Trust sysroot's compiler_builtins (its rlib's objects
# archived and linked before libSystem, as in every Rust binary). Records the binding (nm) and
# the routine bytes' digest (otool), runs each with N random pairs per class, then the MUTANT
# control (a wrong __udivti3 must be reported). Statistical evidence, never a proof.
# Waits while ~/tcg-scratch/quiet.request exists. x86_64 Darwin only.
# usage: run_diff.sh <rustlib dir of the Trust sysroot> <work dir> [N per class, default 20000]
LIB=${1:?rustlib dir, e.g. ~/.local/share/trust-overlays/x86-stage1-ay13556/lib/rustlib/x86_64-apple-darwin/lib}
WORK=${2:?work dir}; N=${3:-20000}
SRC=${0:A:h}
while [ -e ~/tcg-scratch/quiet.request ]; do sleep 30; done
RLIB=$(ls $LIB/libcompiler_builtins-*.rlib | head -1)
mkdir -p $WORK && cd $WORK || exit 9
rm -rf cb && mkdir cb && (cd cb && ar x $RLIB && rm -f lib.rmeta && ar rcs ../libcb.a *.o 2>/dev/null) || exit 8
echo "rlib $(basename $RLIB) sha256 $(shasum -a 256 $RLIB | cut -c1-64)"
sw_vers | tr '\n' ' '; echo; cc --version | head -1
cc -O1 -o diff_sys $SRC/diff_ti3.c || exit 7
cc -O1 -DCB_LINK -o diff_cb $SRC/diff_ti3.c libcb.a || exit 6
cc -O1 -DMUTANT -o diff_sys_mutant $SRC/diff_ti3.c || exit 5
cc -O1 -o off_sys $SRC/offdomain.c || exit 4
cc -O1 -DCB_LINK -o off_cb $SRC/offdomain.c libcb.a || exit 3
for b in diff_sys diff_cb; do
  echo "== $b binding"; nm -m $b | grep -E "_(udiv|umod|div|mod)ti3( |$)"
  for f in ___udivti3 ___umodti3 ___divti3 ___modti3; do
    if nm $b | grep -qE "[tT] $f$"; then
      printf "%s %s bytes sha256 %s\n" $b $f "$(otool -tv -p $f $b | sed -n '3,400p' | awk '/^[0-9a-f]+\t/{print}' | sed 's/^[0-9a-f]*//' | shasum -a 256 | cut -c1-16)"
    fi
  done
done
echo "diff_sys libraries:"; otool -L diff_sys | tail -n +2
for b in diff_sys diff_cb diff_sys_mutant; do echo "== $b"; ./$b $N; echo "exit=$?"; done
for b in off_sys off_cb; do echo "== $b (informational: MIN / -1, off trust-ir's domain)"; ./$b; done
echo RUN-DIFF-DONE
