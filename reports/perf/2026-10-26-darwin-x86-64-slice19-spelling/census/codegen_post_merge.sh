#!/bin/zsh
# The codegen gate again on the branch after merging origin/main 5d732f441 (its irmid change
# reaches trust-cg-codegen), after the library check and the lint run.
S=$HOME/tcg-scratch/s19; W=$HOME/tcg-scratch/wt-s19
until grep -q "CHAIN-LIBCHECK-DONE" $S/logs/chain_libcheck.log 2>/dev/null || ! pgrep -f "[c]hain_libcheck.sh" >/dev/null; do sleep 30; done
until grep -q "TIPPY2-DONE" $S/logs/tippy2.log 2>/dev/null || ! pgrep -f "[t]ippy2.sh" >/dev/null; do sleep 30; done
cd $W
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556
rm -rf $HOME/tcg-scratch/stage1-targets/wt-s19/debug/incremental
TRUST_TARGO=$OV/bin/targo CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s19 TCG_X86_BODY_QUALIFY_AY=$OV/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OV/bin/clean nice -n 19 bash scripts/trust_cargo.sh test --no-fail-fast -p trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus -j2 > $S/logs/gate_codegen_merged.log 2>&1
grep -E "^test result|FAILED" $S/logs/gate_codegen_merged.log | head
echo "CODEGEN-MERGED-DONE $(date)"
