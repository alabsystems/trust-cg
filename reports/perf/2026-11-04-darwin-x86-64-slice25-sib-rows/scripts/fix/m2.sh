#!/bin/bash
# Fix-lane iteration: the slice-25 module and golden writer (module.sh),
# then the slice-25 replay lane with AY/Clean, then the new e2e target.
# Run under build-slot.
bash ~/tcg-scratch/s25-run/fix/scripts/module.sh
source ~/tcg-scratch/s25-run/fix/scripts/env.sh
echo "== qual replay $(date +%H:%M)"
TCG_X86_BODY_QUALIFY_AY=$OV/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OV/bin/clean \
  verify x86_source_bound_body::tests::slice25_qualification::host_qualification_replays_the_slice_twenty_five_body_theorems --test-threads=1 --nocapture
echo "qual-exit=$?"
echo "== e2e $(date +%H:%M)"
TCG_X86_BODY_QUALIFY_AY=$OV/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OV/bin/clean \
  bash scripts/trust_cargo.sh test -p trust-cg-codegen --test e2e_x86_64_sib_rmw -j2 -- --nocapture
echo "e2e-exit=$?"
echo "M2-DONE $(date +%H:%M)"
