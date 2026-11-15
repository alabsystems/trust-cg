#!/usr/bin/env bash
# run.sh [--driver TRUSTC] <first-seed> <count> [opt-levels...]
#
# Every half uses the Trust compiler the bridge pin (channel = "trust") names,
# resolved by scripts/trust_toolchain.py from the PATH trustc/targo package or
# the package trustc named by --driver; the retired stock nightly (which cannot
# load a Trust-built backend) and any unidentified compiler fail the gate. All
# halves compile in Trust's explicit unverified frontend lane (-Ztrust-verify=off),
# a diagnostic lane with no Trust-verified compilation claim.
#
# CROSS-BACKEND calling-convention differential.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# WHY THIS EXISTS: bridge-fuzz, shape-coverage and the beat-llvm corpus all
# compile a WHOLE PROGRAM with one backend. A calling-convention disagreement is
# structurally invisible to them -- caller and callee are both trust-cg, both
# wrong the same way, and they agree. The AArch64 stack-argument layout bug
# (DarwinPCS natural-size packing applied to an ELF target, where AAPCS64 stage
# C.14 mandates 8-byte slots) survived every one of those gates and was found
# only by LINKING ACROSS BACKENDS.
#
# For each seed we build a callee and a caller whose signature overflows the
# argument registers onto the stack, then link three ways:
#
#   llvm x llvm   the ORACLE
#   llvm x tcg    LLVM caller  -> trust-cg callee   (callee reads its args)
#   tcg  x llvm   trust-cg caller -> LLVM callee    (caller writes its args)
#
# Any exit-code difference from the oracle is a P0 ABI mismatch.
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"

gate_result() {
  local expected="$1"
  local observed_match="$2"
  local observed_mismatch="$3"
  local observed_declined="$4"
  local observed_skipped="$5"
  [ "$observed_match" -eq "$expected" ] \
    && [ "$observed_mismatch" -eq 0 ] \
    && [ "$observed_declined" -eq 0 ] \
    && [ "$observed_skipped" -eq 0 ]
}

if [[ "${1:-}" == "--selftest" ]]; then
  gate_result 2 2 0 0 0 || exit 1
  ! gate_result 2 1 0 1 0 || exit 1
  ! gate_result 2 1 0 0 1 || exit 1
  ! gate_result 2 2 1 0 0 || exit 1
  ! gate_result 2 1 0 0 0 || exit 1
  echo "abi-xback result-contract selftest: positive arm + 4 rejection arms"
  exit 0
fi

DRIVER_ARGS=()
if [ "${1:-}" = "--driver" ]; then
  if [ "$#" -lt 2 ]; then
    echo "FAIL: --driver needs a trustc path" >&2
    exit 1
  fi
  DRIVER_ARGS=(--driver "$2")
  shift 2
fi
FIRST=1
COUNT=25
if [ "$#" -gt 0 ]; then
  FIRST="$1"
  shift
fi
if [ "$#" -gt 0 ]; then
  COUNT="$1"
  shift
fi
OPTS=("$@")
[ "${#OPTS[@]}" -eq 0 ] && OPTS=(2)

OUT="${ABI_XBACK_OUT:-$(mktemp -d)}"
mkdir -p "$OUT/fail"
# An unresolvable compiler fails the gate outright rather than falling back to
# some other `rustc`.
if ! RUSTC="$(python3 "$HERE/../../scripts/trust_toolchain.py" ${DRIVER_ARGS[@]+"${DRIVER_ARGS[@]}"} --print compiler)"; then
  echo "FAIL: the pinned Trust compiler is unavailable" >&2
  exit 1
fi
echo "abi-xback: driver $(python3 "$HERE/../../scripts/trust_toolchain.py" --driver "$RUSTC" --print summary)"
if ! HOST_TRIPLE="$(python3 "$HERE/../../scripts/trust_toolchain.py" --driver "$RUSTC" --print host)" \
  || ! SYSROOT="$(python3 "$HERE/../../scripts/trust_toolchain.py" --driver "$RUSTC" --print sysroot)"; then
  echo "FAIL: cannot identify the pinned Trust compiler's host and sysroot" >&2
  exit 1
fi
# The linker is resolved from the compiler's own host triple and printed, never
# inherited from whatever PATH the caller had:
#   *-apple-darwin  the host C driver `cc` (xcrun's, else PATH's), which links
#                   with ld64; both are named by path, ld64 by its `-v`
#                   identity, and `cc` is passed as -Clinker to every link.
#                   No gcc-ld shim is ever put on PATH there.
#   other hosts     trustc's default `cc`, plus the `gcc-ld` shim directory
#                   (`ld.lld` beside `rust-lld`) a Linux GNU link needs on PATH:
#                   the Trust sysroot's first. STOCK EXCEPTION: when the Trust
#                   package ships none, the same host's rustup `stable` shim
#                   (CLAUDE.md lists the Linux gcc-ld shim in the benchmarks
#                   among the stock exceptions; without a shim every link fails
#                   and is counted as a skip, which fails the gate).
LINK=()
case "$HOST_TRIPLE" in
  *-apple-darwin)
    LINKER="$(xcrun --find cc 2>/dev/null || command -v cc || true)"
    LD64="$(xcrun --find ld 2>/dev/null || command -v ld || true)"
    if [ -z "$LINKER" ] || [ ! -x "$LINKER" ] || [ -z "$LD64" ] || [ ! -x "$LD64" ]; then
      echo "FAIL: no host linker for $HOST_TRIPLE: cc='${LINKER}' ld='${LD64}'" >&2
      exit 1
    fi
    LD64_ID="$("$LD64" -v 2>&1 | head -n 1)"
    case "$LD64_ID" in
      *PROGRAM:ld*) ;;
      *)
        echo "FAIL: $LD64 does not identify as Apple ld64: $LD64_ID" >&2
        exit 1
        ;;
    esac
    LINK=(-Clinker="$LINKER")
    echo "abi-xback: host $HOST_TRIPLE; linker $LINKER (ld64 $LD64: $LD64_ID); no gcc-ld shim"
    ;;
  *)
    GCC_LD=""
    for candidate in "$SYSROOT/lib/rustlib/$HOST_TRIPLE/bin/gcc-ld" \
      "$HOME/.rustup/toolchains/stable-$HOST_TRIPLE/lib/rustlib/$HOST_TRIPLE/bin/gcc-ld"; do
      if [ -d "$candidate" ]; then
        GCC_LD="$candidate"
        break
      fi
    done
    if [ -n "$GCC_LD" ]; then
      export PATH="$GCC_LD:$PATH"
      echo "abi-xback: host $HOST_TRIPLE; gcc-ld shim directory on PATH: $GCC_LD"
    else
      echo "abi-xback: host $HOST_TRIPLE; no gcc-ld shim directory for this host"
    fi
    ;;
esac
# The backend is the newest candidate scripts/bridge_backend.py names (or
# ABI_XBACK_DYLIB), and it must be current: a backend older than any input of
# its build would attribute this run to code that is not in the checkout.
if ! DYLIB="$(python3 "$HERE/../../scripts/bridge_backend.py" ${ABI_XBACK_DYLIB:+--backend "$ABI_XBACK_DYLIB"} --print path)"; then
  echo "FAIL: trust-cg backend is unavailable or stale${ABI_XBACK_DYLIB:+: $ABI_XBACK_DYLIB}" >&2
  exit 1
fi
echo "abi-xback: backend $DYLIB"
LIB=(-Ztrust-verify=off --edition=2021 --crate-type staticlib -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1)
BIN=(-Ztrust-verify=off --edition=2021 --crate-type bin -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1 -Cdefault-linker-libraries=y ${LINK[@]+"${LINK[@]}"})
# The trust-cg halves are an ABI differential, not proof evidence: proof
# certificates and the refinement solver are switched off through the
# backend's TRACKED knob option. trustc refuses the former TCG_NO_PROOF_CERTS /
# TCG_REFINE_SOLVER environment variables as untracked codegen controls, which
# turned every trust-cg half into a "declined" compile (320/320 on 2026-09-22)
# and let the gate report zero mismatches over zero executions.
TCG=(-Ztrust-ir-cg-args=no-proof-certs -Ztrust-ir-cg-args=refine-solver=0)
# Every link must use the linker resolved above, not whatever `cc` the
# compiler would pick by default: one probe link with the exact BIN flags
# prints rustc's link line, which must invoke that path.
if [ "${#LINK[@]}" -gt 0 ]; then
  printf 'fn main() {}\n' >"$OUT/link_probe.rs"
  if ! LINK_LINE="$("$RUSTC" "${BIN[@]}" --print link-args -o "$OUT/link_probe" "$OUT/link_probe.rs" 2>"$OUT/link_probe.err")"; then
    echo "FAIL: the link probe did not link: $(head -c 400 "$OUT/link_probe.err")" >&2
    exit 1
  fi
  case "$LINK_LINE" in
    *"\"$LINKER\" "*) ;;
    *)
      echo "FAIL: rustc does not link with the resolved linker $LINKER: $(printf '%s' "$LINK_LINE" | head -c 400)" >&2
      exit 1
      ;;
  esac
  rm -f "$OUT/link_probe" "$OUT/link_probe.rs" "$OUT/link_probe.err"
  echo "abi-xback: link probe: rustc links with $LINKER"
fi

match=0
match_tcg_callee=0
match_tcg_caller=0
mismatch=0
declined=0
skipped=0

for ((seed = FIRST; seed < FIRST + COUNT; seed++)); do
  python3 "$HERE/gen.py" "$seed" callee >"$OUT/callee$seed.rs" 2>/dev/null || {
    skipped=$((skipped + 1))
    continue
  }
  python3 "$HERE/gen.py" "$seed" caller >"$OUT/caller$seed.rs" 2>/dev/null || {
    skipped=$((skipped + 1))
    continue
  }

  for opt in "${OPTS[@]}"; do
    dir="$OUT/s${seed}o${opt}"
    mkdir -p "$dir"

    # --- oracle halves -------------------------------------------------------
    "$RUSTC" "${LIB[@]}" -Copt-level="$opt" -o "$dir/libxl.a" "$OUT/callee$seed.rs" 2>/dev/null || {
      skipped=$((skipped + 1))
      continue
    }
    "$RUSTC" "${BIN[@]}" -Copt-level="$opt" -o "$dir/oracle" "$OUT/caller$seed.rs" -L "$dir" -l static=xl 2>/dev/null || {
      skipped=$((skipped + 1))
      continue
    }
    "$dir/oracle" >/dev/null 2>&1
    want=$?

    # --- trust-cg callee, LLVM caller ---------------------------------------
    # A trust-cg compile failure is the backend declining the half; a failure
    # to link its archive into the LLVM caller is a skipped combination, kept
    # with the linker's diagnostic.
    if ! "$RUSTC" "${LIB[@]}" "${TCG[@]}" -Copt-level="$opt" -Zcodegen-backend="$DYLIB" -o "$dir/libxt.a" "$OUT/callee$seed.rs" 2>"$dir/callee_tcg.err"; then
      declined=$((declined + 1))
      cp "$dir/callee_tcg.err" "$OUT/fail/callee${seed}_O${opt}_tcg.err" 2>/dev/null
      echo "DECLINED llvm-caller x tcg-callee seed=$seed O$opt: $(grep -m1 -E '^error' "$dir/callee_tcg.err" 2>/dev/null | cut -c1-160)"
    elif ! "$RUSTC" "${BIN[@]}" -Copt-level="$opt" -o "$dir/llvm_x_tcg" "$OUT/caller$seed.rs" -L "$dir" -l static=xt 2>"$dir/llvm_x_tcg_link.err"; then
      skipped=$((skipped + 1))
      cp "$dir/llvm_x_tcg_link.err" "$OUT/fail/caller${seed}_O${opt}_llvm_x_tcg_link.err" 2>/dev/null
      echo "SKIPPED llvm-caller x tcg-callee seed=$seed O$opt: link failed: $(grep -m1 -E '^error' "$dir/llvm_x_tcg_link.err" 2>/dev/null | cut -c1-160)"
    else
      "$dir/llvm_x_tcg" >/dev/null 2>&1
      got=$?
      if [ "$got" != "$want" ]; then
        mismatch=$((mismatch + 1))
        cp "$OUT/callee$seed.rs" "$OUT/fail/"
        cp "$OUT/caller$seed.rs" "$OUT/fail/"
        echo "MISMATCH llvm-caller x tcg-callee seed=$seed O$opt: want $want got $got"
      else
        match=$((match + 1))
        match_tcg_callee=$((match_tcg_callee + 1))
      fi
    fi

    # --- trust-cg caller, LLVM callee ---------------------------------------
    # One rustc invocation compiles and links this half; rustc's own
    # `error: linking with` names a link failure (a skip), anything else is
    # the backend declining the caller.
    if "$RUSTC" "${BIN[@]}" "${TCG[@]}" -Copt-level="$opt" -Zcodegen-backend="$DYLIB" -o "$dir/tcg_x_llvm" "$OUT/caller$seed.rs" -L "$dir" -l static=xl 2>"$dir/caller_tcg.err"; then
      "$dir/tcg_x_llvm" >/dev/null 2>&1
      got=$?
      if [ "$got" != "$want" ]; then
        mismatch=$((mismatch + 1))
        cp "$OUT/callee$seed.rs" "$OUT/fail/"
        cp "$OUT/caller$seed.rs" "$OUT/fail/"
        echo "MISMATCH tcg-caller x llvm-callee seed=$seed O$opt: want $want got $got"
      else
        match=$((match + 1))
        match_tcg_caller=$((match_tcg_caller + 1))
      fi
    elif grep -q '^error: linking with `' "$dir/caller_tcg.err" 2>/dev/null; then
      skipped=$((skipped + 1))
      cp "$dir/caller_tcg.err" "$OUT/fail/caller${seed}_O${opt}_tcg_x_llvm_link.err" 2>/dev/null
      echo "SKIPPED tcg-caller x llvm-callee seed=$seed O$opt: link failed: $(grep -m1 -E '^error' "$dir/caller_tcg.err" 2>/dev/null | cut -c1-160)"
    else
      declined=$((declined + 1))
      cp "$dir/caller_tcg.err" "$OUT/fail/caller${seed}_O${opt}_tcg.err" 2>/dev/null
      echo "DECLINED tcg-caller x llvm-callee seed=$seed O$opt: $(grep -m1 -E '^error' "$dir/caller_tcg.err" 2>/dev/null | cut -c1-160)"
    fi
    rm -rf "$dir"
  done
done

echo "abi-xback: $match MATCH, $mismatch MISMATCH, $declined declined, $skipped skipped"
echo "abi-xback: directions: llvm-caller x tcg-callee $match_tcg_callee MATCH; tcg-caller x llvm-callee $match_tcg_caller MATCH; opt levels ${OPTS[*]}; seeds $FIRST..$((FIRST + COUNT - 1))"
echo "artifacts: $OUT"
expected=$((COUNT * ${#OPTS[@]} * 2))
if ! gate_result "$expected" "$match" "$mismatch" "$declined" "$skipped"; then
  echo "FAIL: expected exactly $expected MATCH with no mismatch, decline, or skip" >&2
  exit 1
fi
