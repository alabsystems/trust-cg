#!/usr/bin/env bash
# x86_sroa direct-[StackSlot+disp] promotion regression gate (burn-down S1).
# For each corpus program, compile it TWICE through the same bridge dylib —
# once baseline (promotion OFF) and once with TCG_X86_SROA_DIRECT=1 — and
# assert the exit-code checksum is IDENTICAL. sd01/sd05 (POSITIVE) should
# additionally get faster with the promotion on; the sd02/sd03/sd04/sd06
# adversarial cases MUST stay correct (the pass must refuse or be a no-op);
# sd07 must be declined for compile sanity (and stay correct).
#
# This is the MANDATORY net for the x86_sroa direct-StackSlot extension, which
# has NO translation-validation net — a wrong promotion miscompiles silently.
# Run x2-consistent + at -O0/-O2/-O3 before flipping any default.
#
# Usage (from any cwd): [OPT=3] fuzz/repros/sroa-direct/run_sroa_differential.sh
#   TCG_BRIDGE_DYLIB  librustc_codegen_trust_cg.{so,dylib} to test (default: the
#                     release build under crates/rustc-codegen-trust-cg/target/)
#   TC                rustup toolchain for the bridge (default nightly-2026-04-20)
#   TARGET            optional --target triple (default: host). The promotion is
#                     an x86 lane (TCG_X86_SROA_DIRECT), so run on an x86_64 host.
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(git -C "$HERE" rev-parse --show-toplevel)" || { echo "FATAL: $HERE is not inside a git checkout" >&2; exit 2; }
export PATH="$HOME/.cargo/bin:$PATH"
TC="${TC:-nightly-2026-04-20}"
OPT="${OPT:-3}"
if [[ -n "${TCG_BRIDGE_DYLIB:-}" ]]; then
  DYLIB="$TCG_BRIDGE_DYLIB"
elif [[ -f "$ROOT/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so" ]]; then
  DYLIB="$ROOT/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so"
else
  DYLIB="$ROOT/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
fi
[[ -f "$DYLIB" ]] || { echo "FATAL: dylib not found: $DYLIB (build the bridge --release, or set TCG_BRIDGE_DYLIB)" >&2; exit 2; }
TARGET_FLAGS=(); [[ -n "${TARGET:-}" ]] && TARGET_FLAGS=(--target "$TARGET")

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

compile() { # <src> <sroa:0|1> <bin>
  local src="$1" sroa="$2" bin="$3"
  local pre=(TCG_NO_PROOF_CERTS=1)
  [[ "$sroa" == 1 ]] && pre+=(TCG_X86_SROA_DIRECT=1)
  local od; od=$(mktemp -d)
  env "${pre[@]}" rustup run "$TC" rustc -Zcodegen-backend="$DYLIB" --edition=2021 \
    --crate-type bin ${TARGET_FLAGS[@]+"${TARGET_FLAGS[@]}"} -Cpanic=abort -Coverflow-checks=off \
    -Ccodegen-units=1 -Copt-level="$OPT" --emit=obj -o "$od/o.o" "$src" \
    >/dev/null 2>/dev/null || { rm -rf "$od"; return 1; }
  link "$od" "$bin"; local rc=$?; rm -rf "$od"; return $rc
}

fail=0; compared=0
printf '%-44s  %-6s  %s\n' "PROGRAM" "STATUS" "DETAIL"
printf '%-44s  %-6s  %s\n' "-------" "------" "------"
for src in "$HERE"/sd*.rs; do
  stem=$(basename "$src" .rs)
  b0=$(mktemp); b1=$(mktemp)
  if ! compile "$src" 0 "$b0"; then
    printf '%-44s  %-6s  %s\n' "$stem" "SKIP" "baseline (OFF) fail-closed"
    rm -f "$b0" "$b1"; continue
  fi
  if ! compile "$src" 1 "$b1"; then
    printf '%-44s  %-6s  %s\n' "$stem" "SKIP" "SROA-ON fail-closed"
    rm -f "$b0" "$b1"; continue
  fi
  "$b0" >/dev/null 2>&1; r0=$?
  "$b1" >/dev/null 2>&1; r1=$?
  compared=$((compared+1))
  if [[ "$r0" == "$r1" ]]; then
    printf '%-44s  %-6s  %s\n' "$stem" "OK" "exit=$r0 (sroa on==off)"
  else
    printf '%-44s  %-6s  %s\n' "$stem" "FAIL" "*** MISMATCH off=$r0 on=$r1 ***"
    fail=1
  fi
  rm -f "$b0" "$b1"
done
if [[ $compared == 0 ]]; then echo "=== NO PROGRAMS COMPARED (every compile failed closed) (OPT=$OPT) ==="; exit 2; fi
echo "=== $( [[ $fail == 0 ]] && echo 'ALL CONSISTENT' || echo 'MISMATCH — DO NOT LAND' ) (OPT=$OPT, $compared compared) ==="
exit $fail
