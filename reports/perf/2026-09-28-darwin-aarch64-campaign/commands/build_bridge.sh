#!/bin/bash
set -u
export PATH="$HOME/.cargo/bin:/opt/homebrew/bin:$PATH" ATERM_REROUTE_QUIET=1 CARGO_BUILD_JOBS=3 CARGO_INCREMENTAL=0
PKG="$HOME/Library/Application Support/aterm/pkg/store/trust/9192"
WT=$HOME/trust-cg/.claude/worktrees/agent-workflow
cd "$WT/crates/rustc-codegen-trust-cg" || exit 9
date -u +%FT%TZ
uptime
export CARGO_TARGET_DIR=target-bridge RUSTC="$PKG/bin/trustc"
/usr/bin/time -l "$PKG/bin/targo" --unverified build --release --locked
rc=$?
date -u +%FT%TZ
uptime
echo "exit=$rc"
exit $rc
