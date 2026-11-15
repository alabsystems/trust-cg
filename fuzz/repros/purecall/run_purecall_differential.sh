#!/usr/bin/env bash
# Pure-call-hoist regression gate. For each corpus program, compile it with the
# x86 LICM pure-call tier ON (the default) and OFF (the tracked opt-out
# `-Ztrust-ir-cg-args=no-x86-pure-call-hoist`) through the SAME bridge dylib,
# run both, and require the same exit status.
#
# This is the differential net of the pure-call cluster hoist, which has NO
# translation-validation net: a wrong hoist miscompiles silently (OD-230 fixed
# two such bugs). Besides the exit status it checks, per opt level:
#   * determinism: each arm compiled twice gives byte-identical objects;
#   * must-not-hoist programs (`*must_not_hoist*`): ON and OFF objects are
#     byte-identical, i.e. the tier moved nothing;
#   * non-vacuity: at least one positive program's ON object differs from its
#     OFF object, i.e. the knob reached the tier and the tier fired.
# Every run is bounded by TIMEOUT seconds (a hoisted diverging call hangs).
#
# Usage (from any cwd): [OPTS="1 2 3"] fuzz/repros/purecall/run_purecall_differential.sh
#   TCG_BRIDGE_DYLIB  librustc_codegen_trust_cg.{so,dylib} to test (default: the
#                     release build under crates/rustc-codegen-trust-cg/target/)
#   TRUSTC            the Trust compiler that loads the bridge (default: the
#                     package scripts/trust_toolchain.py resolves; on an x86-64
#                     host, the compiler the bridge was built against)
#   OPTS              opt levels to run (default "1 2 3"; LICM does not run at 0)
#   TIMEOUT           seconds per program run (default 20)
#   TARGET            optional --target triple (default: host). The tier is
#                     x86-only, so run on an x86_64 host or name an x86 target.
# trustc refuses every TCG_*/TRUST_CG_* variable, so the compiles run without
# them (this script's own TCG_BRIDGE_DYLIB included).
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(git -C "$HERE" rev-parse --show-toplevel)" || { echo "FATAL: $HERE is not inside a git checkout" >&2; exit 2; }
TRUSTC="${TRUSTC:-$(python3 -B "$ROOT/scripts/trust_toolchain.py" --print compiler)}" || { echo "FATAL: no installed Trust package resolves" >&2; exit 2; }
OPTS="${OPTS:-${OPT:-1 2 3}}"
TIMEOUT="${TIMEOUT:-20}"
STRIP=(); for v in $(compgen -e); do case "$v" in TCG_*|TRUST_CG_*) STRIP+=(-u "$v");; esac; done
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

compile() { # <src> <hoist:on|off> <opt> <obj>
  local src="$1" arm="$2" opt="$3" obj="$4"
  local knobs=(-Ztrust-ir-cg-args=no-proof-certs)
  [[ "$arm" == off ]] && knobs+=(-Ztrust-ir-cg-args=no-x86-pure-call-hoist)
  env ${STRIP[@]+"${STRIP[@]}"} "$TRUSTC" -Ztrust-verify=off "${knobs[@]}" -Zcodegen-backend="$DYLIB" --edition=2021 \
    --crate-type bin ${TARGET_FLAGS[@]+"${TARGET_FLAGS[@]}"} -Cpanic=abort -Coverflow-checks=off \
    -Ccodegen-units=1 -Copt-level="$opt" --emit=obj -o "$obj" "$src" >/dev/null 2>&1
}

run() { # <bin> -> exit status (128+signal on a signal; 142 = SIGALRM, the timeout)
  perl -e 'alarm shift; exec @ARGV' "$TIMEOUT" "$1" >/dev/null 2>&1
}

fail=0; compared=0
for opt in $OPTS; do
  fired=0
  for src in "$HERE"/pc*.rs; do
    stem=$(basename "$src" .rs)
    w=$(mktemp -d)
    ok=1
    for arm in on off; do
      mkdir -p "$w/$arm.a" "$w/$arm.b"
      compile "$src" "$arm" "$opt" "$w/$arm.a/o.o" && compile "$src" "$arm" "$opt" "$w/$arm.b/o.o" || { ok=0; echo "O$opt $stem  $arm FAILCLOSED"; }
    done
    if [[ $ok == 0 ]]; then
      # Both arms refusing is fail-closed; one arm refusing means the knob
      # changed what the backend admits, which no knob may do.
      if [[ -f "$w/on.b/o.o" || -f "$w/off.b/o.o" ]]; then echo "O$opt $stem  *** ASYMMETRIC REFUSAL ***"; fail=1; fi
      rm -rf "$w"; continue
    fi
    for arm in on off; do
      cmp -s "$w/$arm.a/o.o" "$w/$arm.b/o.o" || { echo "O$opt $stem  *** NONDETERMINISTIC ($arm) ***"; fail=1; }
    done
    if cmp -s "$w/on.a/o.o" "$w/off.a/o.o"; then moved=0; else moved=1; fi
    case "$stem" in
      *must_not_hoist*) [[ $moved == 0 ]] || { echo "O$opt $stem  *** HOISTED (on and off objects differ) ***"; fail=1; } ;;
      *) [[ $moved == 1 ]] && fired=$((fired+1)) ;;
    esac
    link "$w/on.a" "$w/on.bin" && link "$w/off.a" "$w/off.bin" || { echo "O$opt $stem  *** LINK FAILED ***"; fail=1; rm -rf "$w"; continue; }
    run "$w/on.bin"; r1=$?
    run "$w/off.bin"; r0=$?
    compared=$((compared+1))
    if [[ "$r0" == "$r1" ]]; then echo "O$opt $stem  OK   (exit=$r0, moved=$moved)";
    else echo "O$opt $stem  *** MISMATCH off=$r0 on=$r1 ***"; fail=1; fi
    rm -rf "$w"
  done
  if [[ $fired == 0 ]]; then echo "O$opt  *** VACUOUS: no positive program's hoist fired ***"; fail=1; fi
done
if [[ $compared == 0 ]]; then echo "=== NO PROGRAMS COMPARED (every compile failed closed) (OPTS=$OPTS) ==="; exit 2; fi
echo "=== $( [[ $fail == 0 ]] && echo 'ALL CONSISTENT' || echo 'MISMATCH — DO NOT LAND' ) (OPTS=$OPTS, $compared compared) ==="
exit $fail
