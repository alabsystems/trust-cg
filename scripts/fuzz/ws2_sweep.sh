#!/usr/bin/env bash
# Ad-hoc WS2 census over ALL SingleSource/UnitTests single-file programs.
set -u
REF=~/llvm-test-suite-ref
IMP="${IMP:-$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")/../.." && pwd)/target/release/trust-cg-ws2-import}"
WD=$(mktemp -d)
pass=0; unsup=0; crash=0; fail=0; total=0
declare -a FAILED UNSUP CRASHED
for c in "$REF"/SingleSource/UnitTests/*.c; do
  name=$(basename "$c" .c)
  ref="$REF/SingleSource/UnitTests/$name.reference_output"
  [ -f "$ref" ] || continue
  total=$((total+1))
  ll="$WD/$name.ll"; obj="$WD/$name.o"; bin="$WD/$name.bin"
  if ! clang -O0 -S -emit-llvm "$c" -o "$ll" 2>/dev/null; then unsup=$((unsup+1)); UNSUP+=("$name(clang)"); continue; fi
  err=$("$IMP" --opt-level O2 "$ll" "$obj" 2>&1 >/dev/null); rc=$?
  if [ $rc -ne 0 ]; then
    case "$err" in
      unsupported:*) unsup=$((unsup+1)); UNSUP+=("$name") ;;
      *) crash=$((crash+1)); CRASHED+=("$name: $(echo "$err"|head -1)") ;;
    esac; continue
  fi
  if ! cc "$obj" -o "$bin" 2>/dev/null; then crash=$((crash+1)); CRASHED+=("$name(link)"); continue; fi
  out=$("$bin" 2>&1); rc=$?
  # reference_output may include "exit N" convention; compare stdout only
  refnorm=$(sed '/^exit [0-9][0-9]*$/d' "$ref")
  if [ "$(printf '%s' "$out")" == "$(printf '%s' "$refnorm")" ]; then
    pass=$((pass+1))
  else
    fail=$((fail+1)); FAILED+=("$name")
  fi
done
echo "=== WS2 UnitTests census: total=$total pass=$pass unsupported=$unsup crash=$crash FAIL(diff)=$fail ==="
[ ${#FAILED[@]} -gt 0 ] 2>/dev/null && { echo "--- DIFF FAILURES (potential miscompiles!) ---"; printf '%s\n' "${FAILED[@]}"; }
[ ${#CRASHED[@]} -gt 0 ] 2>/dev/null && { echo "--- crashes ---"; printf '%s\n' "${CRASHED[@]:0:10}"; }
[ ${#UNSUP[@]} -gt 0 ] 2>/dev/null && { echo "--- unsupported (first 15) ---"; printf '%s\n' "${UNSUP[@]:0:15}"; }
rm -rf "$WD"
