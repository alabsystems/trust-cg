#!/usr/bin/env bash
# Decisive paired A/B of two backend dylibs on the SAME workload.
# Each round runs A then B back-to-back and differences within the round, so
# machine drift cancels. Reports the distribution of (B - A).
#   usage: dylib_ab.sh <dylib-A> <dylib-B> [rounds] [mode]
#   mode: full (default, compiles an empty program) | meta (--emit=metadata)
set -euo pipefail
A="$1"; B="$2"; N="${3:-41}"; MODE="${4:-full}"
RUSTC="$(rustup which --toolchain nightly-2026-04-20 rustc)"
SCRATCH="${SCRATCH:-/tmp/claude-1000/-home-ayates-trust-cg/06b728f2-f196-4490-9fb3-3291b4078e33/scratchpad}"
W="$SCRATCH/ab"; mkdir -p "$W"; printf 'fn main() {}\n' > "$W/empty.rs"
export TCG_NO_PROOF_CERTS=1 TCG_REFINE_SOLVER=0

python3 - "$A" "$B" "$N" "$RUSTC" "$W" "$MODE" <<'PY'
import subprocess, sys, time, statistics as st
A,B,n,rustc,w,mode = sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4],sys.argv[5],sys.argv[6]
common=["--edition=2021","--crate-type","bin","-Cpanic=abort"]
common += (["--emit=metadata","-o",f"{w}/m.rmeta"] if mode=="meta" else ["-o",f"{w}/e.bin"])
def cmd(so): return ["taskset","-c","18",rustc,f"-Zcodegen-backend={so}",*common,f"{w}/empty.rs"]
def one(argv):
    t0=time.perf_counter(); r=subprocess.run(argv,capture_output=True,text=True)
    dt=(time.perf_counter()-t0)*1000
    if r.returncode!=0: sys.stderr.write(r.stderr[-2000:]); sys.exit(1)
    return dt
ca,cb=cmd(A),cmd(B)
da,db,diff=[],[],[]
for i in range(n+1):
    x=one(ca); y=one(cb)                 # A then B, same round
    if i: da.append(x); db.append(y); diff.append(y-x)
diff.sort(); da.sort(); db.sort()
def q(v,p): return v[int(len(v)*p)]
print(f"  mode      : {mode}   rounds={n}")
print(f"  A  min {da[0]:7.2f}  med {q(da,.5):7.2f} ms   {A.split('/')[-1]}")
print(f"  B  min {db[0]:7.2f}  med {q(db,.5):7.2f} ms   {B.split('/')[-1]}")
print(f"  paired (B-A): med {q(diff,.5):+.2f}  q1 {q(diff,.25):+.2f}  q3 {q(diff,.75):+.2f}  mean {st.mean(diff):+.2f} ms")
neg=sum(1 for d in diff if d<0)
print(f"  B faster in {neg}/{len(diff)} rounds")
PY
