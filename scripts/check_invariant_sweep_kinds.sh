#!/usr/bin/env bash
# Pin `AARCH64_INVARIANT_SWEEP_KINDS` (trust-cg-codegen/src/compiler.rs) against
# reality: compile `fn main() {}` through the bridge with TCG_TIME_SWEEP=1 and
# compare the registry kinds that MISSED the memo with the list the init-time
# speculative sweep warms. The speculative sweep is off for this compile
# (TCG_NO_SPECULATIVE_SWEEP=1) so every invariant kind shows up as a miss.
#
#   scripts/check_invariant_sweep_kinds.sh <rustc> <librustc_codegen_trust_cg.so>
#
# Exit 0: the list covers every registry miss of the empty program and names
# nothing the empty program does not sweep. Exit 1 with a diff otherwise.
set -euo pipefail
rustc="${1:?rustc path}"
dylib="${2:?bridge dylib path}"
repo="$(cd "$(dirname "$0")/.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

printf 'fn main() {}\n' > "$tmp/empty.rs"
TCG_TIME_SWEEP=1 TCG_NO_SPECULATIVE_SWEEP=1 "$rustc" -Zcodegen-backend="$dylib" \
  --edition=2021 --crate-type bin --emit=obj --target aarch64-unknown-linux-gnu \
  -Cpanic=abort -Copt-level=2 "$tmp/empty.rs" -o "$tmp/empty.o" 2> "$tmp/log" \
  || { echo "bridge compile of fn main(){} failed:"; tail -20 "$tmp/log"; exit 2; }

# Registry misses only: RECONSTRUCTED obligations have no registry name.
grep '^TCG_TIME_SWEEP' "$tmp/log" \
  | sed -E 's/^TCG_TIME_SWEEP +[0-9.]+ms (thread=[^ ]+ )?compiled=[a-z]+ ops=[0-9]+ inputs=[0-9]+ width=[0-9]+ cat=[^ ]+ //' \
  | grep -v '^RECONSTRUCTED ' | sort -u > "$tmp/measured"

# The list, as the compiler carries it.
awk '/^pub const AARCH64_INVARIANT_SWEEP_KINDS/,/^\];/' "$repo/crates/trust-cg-codegen/src/compiler.rs" \
  | grep -E '^[[:space:]]+"' \
  | sed -E 's/^[[:space:]]+"(.*)",$/\1/' \
  | sort -u > "$tmp/listed"

if diff -u "$tmp/listed" "$tmp/measured" > "$tmp/diff"; then
  echo "invariant sweep kinds: list == measured ($(wc -l < "$tmp/measured") registry kinds)"
else
  echo "invariant sweep kinds DRIFTED (- listed but not swept, + swept but not listed):"
  cat "$tmp/diff"
  exit 1
fi
