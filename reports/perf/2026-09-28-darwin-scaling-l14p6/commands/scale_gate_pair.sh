#!/bin/bash
# Run benchmarks/beat-llvm/scale_gate.py --rss for the final backend and for
# the baseline backend, recording the load around each run.
set -u
export PATH="$HOME/.cargo/bin:/opt/homebrew/bin:$PATH" ATERM_REROUTE_QUIET=1
S=$SCRATCH/l14p6
WT=$HOME/trust-cg/.claude/worktrees/agent-workflow
PKG="$HOME/Library/Application Support/aterm/pkg/store/trust/9192"
cd "$WT" || exit 9
echo "== after: $(date -u +%FT%TZ) load $(sysctl -n vm.loadavg)"
python3 benchmarks/beat-llvm/scale_gate.py --driver "$PKG/bin/trustc" --rss \
  --dylib "$WT/crates/rustc-codegen-trust-cg/target-bridge/release/librustc_codegen_trust_cg.dylib"
echo "== after done: $(date -u +%FT%TZ) load $(sysctl -n vm.loadavg)"
echo "== before: $(date -u +%FT%TZ) load $(sysctl -n vm.loadavg)"
python3 benchmarks/beat-llvm/scale_gate.py --driver "$PKG/bin/trustc" --rss \
  --dylib "$S/dylib-before/librustc_codegen_trust_cg.dylib" --allow-stale-dylib
echo "== before done: $(date -u +%FT%TZ) load $(sysctl -n vm.loadavg)"
