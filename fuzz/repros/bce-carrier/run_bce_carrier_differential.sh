#!/usr/bin/env bash
# Carrier-arm gate: compile each program arm-OFF vs arm-ON through the same
# dylib; exit codes must be IDENTICAL. OPT env (default 3).
#
# Usage (from any cwd): [OPT=3] fuzz/repros/bce-carrier/run_bce_carrier_differential.sh
#   TCG_BRIDGE_DYLIB  librustc_codegen_trust_cg.{so,dylib} to test (default: the
#                     release build under crates/rustc-codegen-trust-cg/target/)
#   TRUSTC            the Trust compiler that loads the bridge (default: the
#                     package scripts/trust_toolchain.py resolves)
#   TARGET            optional --target triple (default: host). The arm is an
#                     x86 lane (TCG_X86_BCE_CARRIER), so run on an x86_64 host.
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(git -C "$HERE" rev-parse --show-toplevel)" || { echo "FATAL: $HERE is not inside a git checkout" >&2; exit 2; }
# BLOCKED on the Trust toolchain. ALab systems build with Trust (owner
# directive 2026-09-28), and the bridge dylib is built by and loaded into the
# Trust compiler, so the retired stock nightly-2026-04-20 lane this runner used
# can no longer load it. On trustc the arm under test cannot be switched:
# TCG_X86_BCE_CARRIER is read from the environment by trust-cg-opt, and trustc refuses
# every TCG_* variable (measured: "environment variable `TCG_X` is an
# untracked Trust semantic/codegen control"). The arm is also x86-only, and no
# x86_64 Trust package exists (X12). To revive this runner, port the knob to
# -Ztrust-ir-cg-args (crates/rustc-codegen-trust-cg/src/knobs.rs) and run it on
# an x86_64 Trust package; the compile lines below already use trustc.
echo "BLOCKED: $(basename "$0") needs TCG_X86_BCE_CARRIER as a -Ztrust-ir-cg-args knob and an x86_64 Trust package (see the header)" >&2
exit 2
TRUSTC="${TRUSTC:-$(python3 -B "$ROOT/scripts/trust_toolchain.py" --print compiler)}" || { echo "FATAL: no installed Trust package resolves" >&2; exit 2; }
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
run() { local src="$1" arm="$2"; local od; od=$(mktemp -d)
  local pre=(); [[ $arm == on ]] && pre+=(TCG_X86_BCE_CARRIER=1 TCG_X86_BCE_CARRIER_DEBUG=1)
  local elim; elim=$(env ${pre[@]+"${pre[@]}"} "$TRUSTC" -Ztrust-verify=off -Ztrust-ir-cg-args=no-proof-certs -Zcodegen-backend="$DYLIB" --edition=2021 --crate-type bin ${TARGET_FLAGS[@]+"${TARGET_FLAGS[@]}"} -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1 -Copt-level="$OPT" --emit=obj -o "$od/o.o" "$src" 2>&1 1>/dev/null | grep -c "ELIMINATE")
  ls "$od"/*.o >/dev/null 2>&1 || { echo "FC 0"; rm -rf "$od"; return; }
  { echo '#include <stdlib.h>'; nm -u "$od"/*.o 2>/dev/null | while read -r l; do s="${l#U}"; s="${s// /}"; case "$s" in *panic*) c="${s#_}"; echo "void ${c}(void) __asm__(\"${s}\"); void ${c}(void){ abort(); }";; esac; done; } > "$od/s.c"
  cc -o "$od/bin" "$od"/*.o "$od/s.c" 2>/dev/null || { echo "LF 0"; rm -rf "$od"; return; }
  "$od/bin" >/dev/null 2>&1; echo "$? $elim"; rm -rf "$od"; }
fail=0; compared=0
printf "%-40s %-10s %-10s %-6s %s\n" PROG off on ELIMS V
for src in "$HERE"/bc*.rs; do
  stem=$(basename "$src" .rs)
  read o _ < <(run "$src" off); read n e < <(run "$src" on)
  case "$o$n" in
    *FC*|*LF*) v="SKIP (compile/link failed closed)";;
    *) compared=$((compared+1)); [[ "$o" == "$n" ]] && v=OK || { v="*** MISMATCH ***"; fail=1; };;
  esac
  printf "%-40s %-10s %-10s %-6s %s\n" "$stem" "$o" "$n" "$e" "$v"
done
if [[ $compared == 0 ]]; then echo "=== NO PROGRAMS COMPARED (every compile failed closed) OPT=$OPT ==="; exit 2; fi
echo "=== $( [[ $fail == 0 ]] && echo CORRECT || echo 'MISMATCH — DO NOT LAND' ) OPT=$OPT ($compared compared) ==="
exit $fail
