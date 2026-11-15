#!/bin/bash
# The solver-free x86 body suite (gate 1): every x86_source_bound_body test
# but the tool-gated qualification and credit lanes (run one per process
# elsewhere), the negative memo and the canonical migration, as slice 24a's
# gates ran it. MARK (optional) touches a marker once the build is done.
cd ~/tcg-scratch/wt-s25 || exit 9
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s25
git -C ~/tcg-scratch/wt-s25 diff --stat
if [ -n "$MARK" ]; then
  bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 --no-run || { touch ~/tcg-scratch/s25-run/lane/markers/$MARK.built-failed; exit 7; }
  touch ~/tcg-scratch/s25-run/lane/markers/$MARK.built
fi
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- x86_source_bound_body::tests:: --skip negative_memo --skip host_qualification --skip verifier_credits --skip canonical_migration "$@"
echo "suite-exit=$?"
