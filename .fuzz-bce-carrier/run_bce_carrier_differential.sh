#!/usr/bin/env bash
# Carrier-arm gate: compile each program arm-OFF vs arm-ON through the same
# dylib; exit codes must be IDENTICAL. OPT env (default 3).
set -u
WT=/tmp/fbatch-wt
DYLIB="$WT/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
export PATH="$HOME/.cargo/bin:$PATH"
OPT="${OPT:-3}"
run() { local src="$1" arm="$2"; local od; od=$(mktemp -d)
  local pre=(TCG_NO_PROOF_CERTS=1); [[ $arm == on ]] && pre+=(TCG_X86_BCE_CARRIER=1 TCG_X86_BCE_CARRIER_DEBUG=1)
  local elim; elim=$(env "${pre[@]}" rustup run nightly-2026-04-20 rustc -Zcodegen-backend="$DYLIB" --edition=2021 --crate-type bin --target x86_64-apple-darwin -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1 -Copt-level="$OPT" --emit=obj -o "$od/o.o" "$src" 2>&1 1>/dev/null | grep -c "ELIMINATE")
  ls "$od"/*.o >/dev/null 2>&1 || { echo "FC 0"; rm -rf "$od"; return; }
  { echo '#include <stdlib.h>'; nm -u "$od"/*.o 2>/dev/null | while read -r l; do s="${l#U}"; s="${s// /}"; case "$s" in *panic*) c="${s#_}"; echo "void ${c}(void) __asm__(\"${s}\"); void ${c}(void){ abort(); }";; esac; done; } > "$od/s.c"
  cc -o "$od/bin" "$od"/*.o "$od/s.c" 2>/dev/null || { echo "LF 0"; rm -rf "$od"; return; }
  "$od/bin" >/dev/null 2>&1; echo "$? $elim"; rm -rf "$od"; }
fail=0
printf "%-40s %-10s %-10s %-6s %s\n" PROG off on ELIMS V
for src in "$WT"/.fuzz-bce-carrier/bc*.rs; do
  stem=$(basename "$src" .rs)
  read o _ < <(run "$src" off); read n e < <(run "$src" on)
  [[ "$o" == "$n" ]] && v=OK || { v="*** MISMATCH ***"; fail=1; }
  printf "%-40s %-10s %-10s %-6s %s\n" "$stem" "$o" "$n" "$e" "$v"
done
echo "=== $( [[ $fail == 0 ]] && echo CORRECT || echo 'MISMATCH — DO NOT LAND' ) OPT=$OPT ==="
exit $fail
