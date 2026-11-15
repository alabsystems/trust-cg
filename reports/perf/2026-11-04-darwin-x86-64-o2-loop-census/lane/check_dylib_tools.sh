#!/bin/zsh
# Preflight for a census bridge dylib: every built-in tool path the dylib embeds (the
# trust-cg-drat-trim checker built into its OWN tree's target dir) must exist and be
# executable, or the census would silently fall back (2026-11-03: 17 false PASSVAL-067 roots
# after the dylib's worktree was deleted). Usage: check_dylib_tools.sh <dylib>  (exit 0 = ok)
D="${1:?dylib}"
P=$(strings "$D" | grep -oE '/Users/[^ ]*/out/drat-trim' | sort -u)
[ -n "$P" ] || { echo "PREFLIGHT: no embedded drat-trim path found in $D"; exit 5; }
for p in ${(f)P}; do [ -x "$p" ] || { echo "PREFLIGHT FAILED: embedded checker missing: $p"; exit 5; }; done
echo "preflight ok: $P"
