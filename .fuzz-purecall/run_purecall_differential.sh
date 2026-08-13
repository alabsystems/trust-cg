#!/usr/bin/env bash
# Pure-call-hoist regression gate. For each corpus program, compile it TWICE
# through the same bridge dylib — once with the hoist OFF (baseline) and once
# with it ON — and assert the exit-code checksum is IDENTICAL. The positive case
# (pc01) additionally SHOULD get faster with the hoist on; the pc02..pc05
# adversarial cases MUST stay correct (the hoist must refuse or be a no-op).
#
# This is the MANDATORY net for Piece 2 (x86_licm pure-call cluster hoist), which
# has NO translation-validation net — a wrong hoist miscompiles silently. Run
# x2-consistent + at -O0/-O2/-O3 before flipping TCG_PURE_CALL_HOIST default-on.
#
# Usage: [OPT=3] .fuzz-purecall/run_purecall_differential.sh
set -u
WT=/tmp/fbatch-wt
DYLIB="$WT/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
TC=nightly-2026-04-20
TARGET=x86_64-apple-darwin
OPT="${OPT:-3}"
[[ -f "$DYLIB" ]] || { echo "FATAL: dylib not found: $DYLIB"; exit 2; }

link() { # <objdir> <bin>
  local od="$1" bin="$2"; local objs=("$od"/*.o)
  [[ -e "${objs[0]}" ]] || return 1
  local stubs="$od/stubs.c"
  { echo '#include <stdlib.h>'
    nm -u "${objs[@]}" 2>/dev/null | while read -r l; do
      s="${l#U}"; s="${s// /}"
      case "$s" in *panic*) c="${s#_}";
        echo "void ${c}(void) __asm__(\"${s}\"); void ${c}(void){ abort(); }";; esac
    done; } > "$stubs"
  cc -o "$bin" "${objs[@]}" "$stubs" 2>/dev/null
}

compile() { # <src> <hoist:0|1> <bin>
  local src="$1" hoist="$2" bin="$3"
  local pre=(TCG_NO_PROOF_CERTS=1 TCG_PURE_FN_ANALYSIS=1)
  [[ "$hoist" == 1 ]] && pre+=(TCG_PURE_CALL_HOIST=1)
  local od; od=$(mktemp -d)
  env "${pre[@]}" rustup run "$TC" rustc -Zcodegen-backend="$DYLIB" --edition=2021 \
    --crate-type bin --target "$TARGET" -Cpanic=abort -Coverflow-checks=off \
    -Ccodegen-units=1 -Copt-level="$OPT" --emit=obj -o "$od/o.o" "$src" \
    >/dev/null 2>/dev/null || { rm -rf "$od"; return 1; }
  link "$od" "$bin"; local rc=$?; rm -rf "$od"; return $rc
}

fail=0
for src in "$WT"/.fuzz-purecall/pc*.rs; do
  stem=$(basename "$src" .rs)
  b0=$(mktemp); b1=$(mktemp)
  if ! compile "$src" 0 "$b0"; then echo "$stem  OFF FAILCLOSED"; rm -f "$b0" "$b1"; continue; fi
  if ! compile "$src" 1 "$b1"; then echo "$stem  ON  FAILCLOSED"; rm -f "$b0" "$b1"; continue; fi
  "$b0" >/dev/null 2>&1; r0=$?
  "$b1" >/dev/null 2>&1; r1=$?
  if [[ "$r0" == "$r1" ]]; then echo "$stem  OK   (exit=$r0, hoist on==off)";
  else echo "$stem  *** MISMATCH off=$r0 on=$r1 ***"; fail=1; fi
  rm -f "$b0" "$b1"
done
echo "=== $( [[ $fail == 0 ]] && echo 'ALL CONSISTENT' || echo 'MISMATCH — DO NOT LAND' ) (OPT=$OPT) ==="
exit $fail
