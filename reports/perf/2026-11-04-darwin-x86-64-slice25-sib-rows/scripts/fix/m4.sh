#!/bin/bash
# Fix-lane iteration: the slice-25 module (golden checked, not written) and
# the new e2e target. Run under build-slot.
source ~/tcg-scratch/s25-run/fix/scripts/env.sh
git -C ~/tcg-scratch/wt-s25 status --short
echo "== module $(date +%H:%M)"
verify x86_source_bound_body::tests::slice25:: --nocapture
echo "module-exit=$?"
echo "== e2e $(date +%H:%M)"
TCG_X86_BODY_QUALIFY_AY=$OV/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OV/bin/clean \
  bash scripts/trust_cargo.sh test -p trust-cg-codegen --test e2e_x86_64_sib_rmw -j2 -- --nocapture
echo "e2e-exit=$?"
echo "M4-DONE $(date +%H:%M)"
