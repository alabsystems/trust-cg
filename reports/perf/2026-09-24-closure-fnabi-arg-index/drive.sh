#!/usr/bin/env bash
# The m142 closure-argument reproducer: two shapes, two refusals, ~1s each.
#
#   ./drive.sh "<label>" /path/to/librustc_codegen_trust_cg.so
#
# It compiles the callee rlib with the LLVM backend (the oracle half of the
# m142 differential) and then compiles each caller with the trust-cg backend
# dylib under test. Both callers are EXPECTED to refuse: `[TCG-ARG-ABI]` is the
# by-value-argument placement gate, and `scalar_pair_param_plan` declines a
# `ty::Closure` instance by name (closure call sites are hand-built one value
# per argument), so the closure body's own `Option<u8>` `PassMode::Pair`
# parameter keeps the whole-slot declaration and the gate refuses it. That
# decline is the still-open scope question, recorded under XD-05.
#
# WHAT THIS SCRIPT IS EVIDENCE FOR is the OTHER line: before the argument-index
# fix, `apply_once` (a NON-capturing `FnOnce` closure, whose zero-sized env the
# bridge declaration drops while rustc keeps it as `FnAbi::args[0]`) reported
# `rustc's FnAbi argument 0 is Closure(..) ... Report this — it is a bridge bug`
# instead. Afterwards both shapes report the same honest lane refusal.
#
# TRUSTC defaults to the stage2 driver this was measured with.
set -u
LABEL="${1:?usage: drive.sh <label> <backend dylib>}"
DY="${2:?usage: drive.sh <label> <backend dylib>}"
T="${TRUSTC:-$HOME/trust/build/x86_64-unknown-linux-gnu/stage2/bin/trustc}"
HERE="$(cd "$(dirname "$0")" && pwd)"
OUT="$(mktemp -d "${TMPDIR:-/tmp}/m142-closure-argindex.XXXXXX")"
trap 'rm -rf "$OUT"' EXIT
"$T" --edition=2021 -Ztrust-verify=off --crate-type rlib --crate-name calleearg \
   --target x86_64-unknown-linux-gnu -Cpanic=abort -Coverflow-checks=off \
   -Ccodegen-units=1 -Copt-level=0 --out-dir "$OUT" "$HERE/calleearg.rs" >/dev/null 2>&1
echo "# $LABEL"
echo "# backend sha256 $(sha256sum "$DY" | cut -c1-12)…  stage2 trustc $("$T" -vV | sed -n 's/^commit-hash: \(.\{9\}\).*/\1/p')  -Copt-level=0"
for shape in apply_fn apply_once; do
  LOG="$OUT/$shape.log"
  "$T" --edition=2021 -Ztrust-verify=off --crate-type bin -Zcodegen-backend="$DY" \
     --target x86_64-unknown-linux-gnu -Cpanic=abort -Coverflow-checks=off \
     -Ccodegen-units=1 -Copt-level=0 \
     --extern "calleearg=$OUT/libcalleearg.rlib" -L "$OUT" -o "$OUT/caller_$shape" \
     "$HERE/caller_$shape.rs" >"$LOG" 2>&1
  RC=$?
  echo ""
  echo "## O0 $shape, trust-cg caller (rustc exit $RC)"
  grep -o '\[TCG-ARG-ABI\].*' "$LOG" | head -1 | cut -c1-760
  echo "   distinct TCG codes in the log: $(grep -o '\[TCG-[A-Z0-9-]*\]' "$LOG" | sort -u | tr '\n' ' ')"
  echo "   'it is a bridge bug' occurrences: $(grep -c 'it is a bridge bug' "$LOG")"
done
