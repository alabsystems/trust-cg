#!/bin/bash
# The slice-25 solver-free module on the fix tree (--nocapture: the
# S25_SPLIT and S25_MUTANT lines), then the golden writer (it rewrites the
# golden and panics with the digest to pin). Run under build-slot.
source ~/tcg-scratch/s25-run/fix/scripts/env.sh
git -C ~/tcg-scratch/wt-s25 status --short
echo "== module $(date +%H:%M)"
verify x86_source_bound_body::tests::slice25:: --nocapture --skip slice_twenty_five_smt2_is_canonical_per_shape
echo "module-exit=$?"
if [ -n "$WRITE" ]; then
  echo "== golden write $(date +%H:%M)"
  TCG_X86_BODY_SNAPSHOT_WRITE=1 verify x86_source_bound_body::tests::slice25::slice_twenty_five_smt2_is_canonical_per_shape --nocapture
  echo "golden-exit=$?"
fi
echo "MODULE-DONE $(date +%H:%M)"
