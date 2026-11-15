#!/bin/bash
# One tool-gated test per process on the qualification pair (AY 13556 +
# Clean 5f09e36c from the t011 overlay). Usage: qual.sh <exact test path>...
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
export TCG_X86_BODY_QUALIFY_AY=$OV/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OV/bin/clean
status=0
for t in "$@"; do
  echo "=== $t $(date +%H:%M:%S)"
  bash ~/tcg-scratch/s24a-run/scripts/run.sh "$t" --exact --test-threads=1 --nocapture || status=1
done
exit $status
