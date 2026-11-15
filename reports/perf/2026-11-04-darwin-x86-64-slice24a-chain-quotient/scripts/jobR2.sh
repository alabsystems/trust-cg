#!/bin/bash
# Review round, gates 1, 2 (the replay lane) and 4 on the committed head: the
# solver-free x86 body suite, the slice-24a replay lane, then
# trust-cg-codegen's body and must-refuse targets with the AY/Clean pair.
S=~/tcg-scratch/s24a-run/scripts
P=x86_source_bound_body::tests
echo "== gate1 $(date +%H:%M) at $(git -C ~/tcg-scratch/wt-s24a rev-parse HEAD)"
bash $S/run.sh $P:: --skip negative_memo --skip host_qualification --skip verifier_credits --skip canonical_migration
echo "== gate2 replay $(date +%H:%M)"
bash $S/qual.sh $P::slice24_qualification::host_qualification_replays_the_slice_twenty_four_body_theorems
echo "== gate4 $(date +%H:%M)"
cd ~/tcg-scratch/wt-s24a || exit 9
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
export TRUST_TARGO=$OV/bin/targo CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s24a
TCG_X86_BODY_QUALIFY_AY=$OV/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OV/bin/clean \
  bash scripts/trust_cargo.sh test -p trust-cg-codegen -j2 --test x86_source_bound_body --test must_refuse_corpus --no-fail-fast
echo "JOB-R2-DONE $(date +%H:%M)"
