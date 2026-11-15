#!/bin/zsh
# Census chain for main 7ee0def54 (post-OD-225): one release bridge from a KEPT detached worktree
# (its dylib embeds that tree's drat-trim path; keep ~/tcg-scratch/wt-census-7ee0 until the dylib
# is retired), then the O2 and O0 core proof censuses from the same dylib.
W=$HOME/tcg-scratch/wt-census-7ee0
unset CARGO_TARGET_DIR
STAMP=$(mktemp); sleep 1
echo "bridge build $(date +%H:%M) at $(git -C $W rev-parse --short HEAD)"
BOUT=$(~/tcg-scratch/build_bridge.t011.sh "$W"); echo "$BOUT"
echo "$BOUT" | grep -qx "EXIT=0" || { echo "bridge build failed"; exit 3; }
D="$W/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
[ -f "$D" ] && [ "$D" -nt "$STAMP" ] || { echo "no fresh dylib: $D"; exit 3; }
echo "== O2"; ~/tcg-scratch/census_t011_dylib.sh "$D" o2-7ee0 2 || echo "O2 census rc=$?"
echo "== O0"; ~/tcg-scratch/census_t011_dylib.sh "$D" o0-7ee0 0 || echo "O0 census rc=$?"
echo CHAIN-DONE
