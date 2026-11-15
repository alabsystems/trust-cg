cd ~/tcg-scratch/wt-od233 || exit 9
BIN=$HOME/tcg-scratch/stage1-targets/wt-od233-own/debug/build/trust-cg-verify/8cf31e2294489925/out/trust_cg_verify-8cf31e2294489925
T=x86_source_bound_body::tests::od233::od233_diagnose_the_every_point_overflow
ls -l $BIN
echo "== BIG-STACK run"
RUST_MIN_STACK=536870912 $BIN $T --exact --include-ignored --nocapture 2>&1 | grep -v "^DIAG" | tail -5
echo "== BIG-STACK-RC=${PIPESTATUS[0]}"
echo "== LLDB run"
lldb --batch -o "run" -k "thread backtrace" -k "quit" -- $BIN $T --exact --include-ignored --nocapture > ~/tcg-scratch/od233-run/logs/a08-bt.txt 2>&1
echo "== LLDB-RC=$?"
grep -c "frame #" ~/tcg-scratch/od233-run/logs/a08-bt.txt
