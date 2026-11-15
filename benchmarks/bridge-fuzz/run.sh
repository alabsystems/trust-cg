#!/usr/bin/env bash
# run.sh [--driver TRUSTC] <first-seed> <count> [opt-levels...]
#
# Generative differential gate for the RUSTC BRIDGE. For each seed: generate a
# deterministic, UB-free safe-Rust program, compile it with trustc's LLVM backend
# (the ORACLE) and with trust-cg, run both, compare exit status.
#
#   WRONG-ANSWER  exit codes differ            -> P0, program kept
#   NONDET        trust-cg differs run to run  -> P0, program kept
#   DECLINED      trust-cg failed closed       -> tracked, not a defect
#   MATCH         agree
#
# Both sides use the Trust compiler the bridge pin (channel = "trust") names,
# resolved by scripts/trust_toolchain.py from the PATH trustc/targo package or
# the package trustc named by --driver. The retired stock nightly, any
# unidentified compiler, and a bare `rustc` fallback are refused (exit 2). Both
# sides compile in Trust's explicit unverified frontend lane (-Ztrust-verify=off),
# a diagnostic lane with no Trust-verified compilation claim.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
DRIVER_ARGS=()
if [ "${1:-}" = "--driver" ]; then
  [ "$#" -ge 2 ] || { echo "bridge-fuzz: FATAL: --driver needs a trustc path" >&2; exit 2; }
  DRIVER_ARGS=(--driver "$2"); shift 2
fi
FIRST="${1:-1}"; COUNT="${2:-25}"; shift 2 2>/dev/null || true
OPTS=("$@"); [ ${#OPTS[@]} -eq 0 ] && OPTS=(3)
OUT="${BRIDGE_FUZZ_OUT:-$(mktemp -d)}"; mkdir -p "$OUT/fail"
case "$(uname -s)" in Darwin) _EXT=dylib ;; *) _EXT=so ;; esac
DYLIB="${BRIDGE_FUZZ_DYLIB:-$HERE/../../crates/rustc-codegen-trust-cg/target-bridge/release/librustc_codegen_trust_cg.$_EXT}"
# Fail LOUDLY on a missing backend. A nonexistent dylib makes every trust-cg
# compile fail, which this script would otherwise count as `declined` -- so a
# misconfigured run reports "0 WRONG-ANSWER" and looks like a clean sweep while
# having tested nothing. That exact false all-clear happened: the old default
# pointed at `target/` (not `target-bridge/`) with a hardcoded Linux `.so`, so
# on macOS it could never resolve, and a 80-seed run came back "80 declined".
if [ ! -f "$DYLIB" ]; then
  echo "bridge-fuzz: FATAL: no backend dylib at $DYLIB" >&2
  echo "  build it:  (cd $HERE/../../crates/rustc-codegen-trust-cg && CARGO_TARGET_DIR=target-bridge \\" >&2
  echo "              RUSTC=<trust-package>/bin/trustc <trust-package>/bin/targo --unverified build --release)" >&2
  echo "  or set BRIDGE_FUZZ_DYLIB=/path/to/librustc_codegen_trust_cg.$_EXT" >&2
  exit 2
fi
# Fail LOUDLY on a STALE backend too. A dylib older than the backend sources
# fuzzes some OTHER compiler and reports the result against this tree: on
# 2026-09-16 the dylib on disk was 517 commits behind HEAD, and a sweep over it
# would have printed a clean "0 WRONG-ANSWER" for code it never exercised.
# Mirrors run.py / compile_gate.py / scale_gate.py (tests, benches and examples
# are not compiled into the cdylib and cannot make it stale).
if [ -z "${BRIDGE_FUZZ_ALLOW_STALE:-}" ]; then
  STALE_SRC="$(find "$HERE/../../crates" -name '*.rs' -newer "$DYLIB" \
      -not -path '*/target*' -not -path '*/tests/*' -not -path '*/benches/*' \
      -not -path '*/examples/*' -print -quit 2>/dev/null)"
  if [ -n "$STALE_SRC" ]; then
    echo "bridge-fuzz: FATAL: backend dylib is STALE ($STALE_SRC is newer)." >&2
    echo "  rebuild it, or set BRIDGE_FUZZ_ALLOW_STALE=1 to sweep anyway (NOT evidence)." >&2
    exit 2
  fi
fi
# STOCK EXCEPTION (Trust lacks rust-lld/gcc-ld; measured: no lib/rustlib/<host>/bin/{rust-lld,gcc-ld} in the Trust sysroot): the Linux linker shim comes from the stock stable toolchain's gcc-ld; the compilers come from scripts/trust_toolchain.py.
export PATH="$HOME/.rustup/toolchains/stable-aarch64-unknown-linux-gnu/lib/rustlib/aarch64-unknown-linux-gnu/bin/gcc-ld:$PATH"
RUSTC="$(python3 "$HERE/../../scripts/trust_toolchain.py" ${DRIVER_ARGS[@]+"${DRIVER_ARGS[@]}"} --print compiler)" || {
  echo "bridge-fuzz: FATAL: cannot resolve the pinned Trust compiler" >&2; exit 2; }
echo "bridge-fuzz: driver $(python3 "$HERE/../../scripts/trust_toolchain.py" --driver "$RUSTC" --print summary)"
BASE="-Ztrust-verify=off --edition=2021 --crate-type bin -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1 -Cdefault-linker-libraries=y"
# trust-cg halves switch proof certificates and the refinement solver off
# through the backend's TRACKED knob option; trustc refuses the former
# TCG_NO_PROOF_CERTS / TCG_REFINE_SOLVER environment variables as untracked
# codegen controls, which made every trust-cg compile fail (2026-09-22).
match=0; wrong=0; declined=0; nondet=0; genfail=0
for ((s=FIRST; s<FIRST+COUNT; s++)); do
  src="$OUT/g$s.rs"
  python3 "$HERE/gen.py" "$s" > "$src" 2>/dev/null || { genfail=$((genfail+1)); continue; }
  for o in "${OPTS[@]}"; do
    if ! "$RUSTC" $BASE -Copt-level=$o -o "$OUT/l$s" "$src" 2>"$OUT/l$s.err"; then
      genfail=$((genfail+1)); continue
    fi
    "$OUT/l$s" >/dev/null 2>&1; le=$?
    if ! "$RUSTC" $BASE -Ztrust-ir-cg-args=no-proof-certs -Ztrust-ir-cg-args=refine-solver=0 -Copt-level=$o \
         -Zcodegen-backend="$DYLIB" -o "$OUT/t$s" "$src" 2>"$OUT/t$s.err"; then
      declined=$((declined+1)); continue
    fi
    "$OUT/t$s" >/dev/null 2>&1; t1=$?
    "$OUT/t$s" >/dev/null 2>&1; t2=$?
    if [ "$t1" != "$t2" ]; then
      nondet=$((nondet+1)); cp "$src" "$OUT/fail/nondet_s${s}_O$o.rs"
      echo "NONDET  seed=$s O$o  tcg=$t1 then $t2 (llvm=$le)"
    elif [ "$le" != "$t1" ]; then
      wrong=$((wrong+1)); cp "$src" "$OUT/fail/wrong_s${s}_O$o.rs"
      echo "WRONG-ANSWER  seed=$s O$o  llvm=$le tcg=$t1"
    else
      match=$((match+1))
    fi
  done
done
echo "bridge-fuzz: $match MATCH, $wrong WRONG-ANSWER, $nondet NONDET, $declined declined, $genfail gen/oracle-fail"
echo "artifacts: $OUT"
[ $wrong -gt 0 ] || [ $nondet -gt 0 ] && exit 1
exit 0
