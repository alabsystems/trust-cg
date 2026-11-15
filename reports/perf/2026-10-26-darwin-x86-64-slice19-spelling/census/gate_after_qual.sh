#!/bin/zsh
# The solver-free body gate on the final binary, after the qualification (no AY of its own:
# the negative-memo controls run fixture solvers, which replay19.py's gate waits on).
S=$HOME/tcg-scratch/s19
until grep -q "QUAL-DONE" $S/logs/chain_meas5.log 2>/dev/null || ! pgrep -f "[c]hain_meas5.sh" >/dev/null; do sleep 30; done
cd $HOME/tcg-scratch/wt-s19/crates/trust-cg-verify
RUST_MIN_STACK=67108864 nice -n 19 $S/testbin_final3 x86_source_bound_body::tests:: --skip host_qualification --skip verifier_credits --skip canonical_migration_pairs --test-threads=2 > $S/logs/gate_final3.log 2>&1
grep -E "^test result|FAILED" $S/logs/gate_final3.log | head -20
echo "GATE-FINAL3-DONE $(date)"
