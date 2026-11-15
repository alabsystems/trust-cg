#!/bin/zsh
# Gates for lane/o2-pass-knobs (tracked opt-outs for five x86 O2 passes). Run under build-slot.
# Touches trust-cg-opt, trust-cg-codegen and the bridge; runs those crates' tests that cover
# the changed code, fmt, tippy, docs, and a release bridge build (the attribution census's dylib).
W=$HOME/tcg-scratch/wt-knobs
cd $W || exit 9
unset CARGO_TARGET_DIR
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
export TRUST_TARGO=$OV/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-knobs
fail() { echo "GATE RED: $1"; exit 1; }
echo "opt tests $(date +%H:%M)"
bash scripts/trust_cargo.sh test -p trust-cg-opt --test x86_pass_opt_out_installers -j2 2>&1 | tail -4 | tee /dev/stderr | grep -q "test result: ok" || fail "installer test"
O=$(bash scripts/trust_cargo.sh test -p trust-cg-opt --lib -j2 -- x86_block_merge:: x86_rotate:: x86_peephole:: 2>&1)
echo "$O" | grep -E "^test result"; echo "$O" | grep -q "^test result: ok" && ! echo "$O" | grep -q "FAILED" || { echo "$O" | grep -E "FAILED|panicked" | head; fail "opt lib tests"; }
echo "codegen check $(date +%H:%M)"
# Not --tests: the kernel-JIT fixture targets (e2e_lazy_delta, ...) refuse to compile on any compiler but
# their pinned identities ("kernel JIT fixtures require exact Rust ..."), which this host's overlay is not.
bash scripts/trust_cargo.sh check -p trust-cg-codegen --lib --test x86_source_bound_body --test must_refuse_corpus -j2 > ~/tcg-scratch/runs/knobs-codegen-check.log 2>&1 || { grep -E "^error" ~/tcg-scratch/runs/knobs-codegen-check.log | head; fail "codegen check"; }
echo "fmt/docs $(date +%H:%M)"
TRUST_TARGO="$HOME/Library/Application Support/aterm/pkg/store/trust/6808/bin/targo" bash scripts/check_fmt.sh 2>&1 | tail -1 | grep -q "check_fmt: OK" || fail "fmt"
python3 scripts/check_documentation.py --check 2>&1 | tail -1 | grep -q "Maintained file links" || fail "docs"
echo "tippy $(date +%H:%M)"
bash scripts/check_tippy.sh > ~/tcg-scratch/runs/tippy-knobs.log 2>&1; T=$?
tail -3 ~/tcg-scratch/runs/tippy-knobs.log
# On this host the lint frontend is unavailable, not green: the t011 overlay targo has no `tippy`
# subcommand and the package targo (6808) cannot resolve AY 7ed2ea1da's manifests. Only that exact
# condition is reported as UNAVAILABLE; any real finding fails the gate.
if [ $T -ne 0 ]; then
  if [ "$(grep -c 'RED — ' ~/tcg-scratch/runs/tippy-knobs.log)" -gt 0 ] && [ "$(grep -c '^error: no such command: `tippy`' ~/tcg-scratch/runs/tippy-knobs.log)" -eq "$(grep -cE '^check_tippy: RED — [a-z0-9-]+ \(' ~/tcg-scratch/runs/tippy-knobs.log)" ]; then
    echo "TIPPY UNAVAILABLE on this host (no tippy frontend for the t011 overlay); not a pass"
  else
    fail "tippy (see runs/tippy-knobs.log)"
  fi
fi
echo "bridge $(date +%H:%M)"
unset CARGO_TARGET_DIR TRUST_TARGO
STAMP=$(mktemp); sleep 1
BOUT=$(~/tcg-scratch/build_bridge.t011.sh "$W"); echo "$BOUT"
echo "$BOUT" | grep -qx "EXIT=0" || fail "bridge build"
D="$W/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
[ -f "$D" ] && [ "$D" -nt "$STAMP" ] || fail "no fresh bridge dylib"
cp "$D" ~/tcg-scratch/runs/knobs.dylib && shasum -a 256 ~/tcg-scratch/runs/knobs.dylib
echo "KNOB GATES GREEN $(date +%H:%M)"
