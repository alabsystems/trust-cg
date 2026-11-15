#!/bin/bash
# decomp.sh <dylib> <prog> <N>: peak-RSS decomposition of one corpus program.
S=$SCRATCH/l14p10
TC="$HOME/Library/Application Support/aterm/pkg/store/trust/9192/bin/trustc"
D="$1"; P="$2"; N="${3:-5}"
SRC=$HOME/trust-cg/.claude/worktrees/agent-workflow/benchmarks/beat-llvm/progs/$P.rs
O="$S/vm/decomp"; mkdir -p "$O"
export MACOSX_DEPLOYMENT_TARGET=13.0
COMMON=(-Ztrust-verify=off --edition=2021 --crate-type bin --target aarch64-apple-darwin -Cpanic=abort)
python3 "$S/pm.py" "$N" "llvm -O2 metadata-only" -- "$TC" "${COMMON[@]}" -Copt-level=2 --emit=metadata -o "$O/a.rmeta" "$SRC"
python3 "$S/pm.py" "$N" "bridge metadata-only" -- "$TC" "-Zcodegen-backend=$D" "${COMMON[@]}" -Copt-level=3 --emit=metadata -o "$O/b.rmeta" "$SRC"
python3 "$S/pm.py" "$N" "llvm -O2" -- "$TC" "${COMMON[@]}" -Copt-level=2 -o "$O/a" "$SRC"
python3 "$S/pm.py" "$N" "llvm -O3" -- "$TC" "${COMMON[@]}" -Copt-level=3 -o "$O/a3" "$SRC"
python3 "$S/pm.py" "$N" "bridge production (default knobs)" -- "$TC" "-Zcodegen-backend=$D" "${COMMON[@]}" -Copt-level=3 -o "$O/b0" "$SRC"
python3 "$S/pm.py" "$N" "bridge no-proof-certs" -- "$TC" "-Zcodegen-backend=$D" "-Ztrust-ir-cg-args=no-proof-certs" "${COMMON[@]}" -Copt-level=3 -o "$O/b" "$SRC"
