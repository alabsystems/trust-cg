#!/usr/bin/env bash
# Measure dylib load cost for a candidate build of the rustc backend dylib.
#   usage: dylib_load_bench.sh <label> <dylib-path> [N_rustc] [N_dlopen]
#
# Two instruments:
#   1. dlopen microbench  — isolates pure load cost (mmap + relocation +
#      symbol binding), very low noise. Primary signal.
#   2. rustc empty-program — the headline end-to-end number, noisy; LLVM and
#      trust-cg lanes are interleaved so machine drift cancels.
set -euo pipefail
LABEL="$1"; DYLIB="$2"; NR="${3:-15}"; ND="${4:-25}"
RUSTC="$(rustup which --toolchain nightly-2026-04-20 rustc)"
SCRATCH="${SCRATCH:-/tmp/claude-1000/-home-ayates-trust-cg/06b728f2-f196-4490-9fb3-3291b4078e33/scratchpad}"
WORK="$SCRATCH/bench"; mkdir -p "$WORK"
printf 'fn main() {}\n' > "$WORK/empty.rs"

export TCG_NO_PROOF_CERTS=1 TCG_REFINE_SOLVER=0

# ---- instrument 1: pure dlopen ----
DL=$(taskset -c 18 "$SCRATCH/dlbench" "$DYLIB" "$ND" 2>/dev/null)

# ---- instrument 1b: in-rustc load cost.  `--emit=metadata` makes rustc
# dlopen + construct the backend but run no codegen, so the delta against the
# same command without -Zcodegen-backend is pure load cost. Baseline is ~11ms
# instead of ~74ms, which makes this ~10x more sensitive than instrument 2. ----
LOADC=$(python3 - "$NR" "$RUSTC" "$DYLIB" "$WORK" <<'PY'
import subprocess, sys, time
n=int(sys.argv[1]); rustc=sys.argv[2]; dylib=sys.argv[3]; work=sys.argv[4]
common=["--edition=2021","--crate-type","bin","-Cpanic=abort","--emit=metadata",
        "-o",f"{work}/m.rmeta",f"{work}/empty.rs"]
off=["taskset","-c","18",rustc,*common]
on =["taskset","-c","18",rustc,f"-Zcodegen-backend={dylib}",*common]
def one(argv):
    t0=time.perf_counter(); r=subprocess.run(argv,capture_output=True,text=True)
    dt=(time.perf_counter()-t0)*1000
    if r.returncode!=0: sys.stderr.write(r.stderr[-3000:]); sys.exit(1)
    return dt
# PAIRED differences: run off/on back-to-back each round and difference within
# the round, so slow drift (thermal, neighbour load) cancels instead of showing
# up as signal.  min-of-mins across separate pools does NOT cancel drift and
# produced negative "load costs" -- hence the pairing.
n=max(n,31)
diffs=[]; offs=[]
for i in range(n+1):
    a=one(off); b=one(on)
    if i: diffs.append(b-a); offs.append(a)
diffs.sort(); offs.sort()
print(f"{offs[0]:.2f} {diffs[len(diffs)//2]:.2f} {diffs[len(diffs)//4]:.2f}")
PY
)
read MOFF MLOAD MLOADQ1 <<<"$LOADC"

# ---- instrument 2: rustc, lanes interleaved ----
RUSTC_T=$(python3 - "$NR" "$RUSTC" "$DYLIB" "$WORK" <<'PY'
import subprocess, sys, time
n=int(sys.argv[1]); rustc=sys.argv[2]; dylib=sys.argv[3]; work=sys.argv[4]
common=["--edition=2021","--crate-type","bin","-Cpanic=abort"]
lanes={
 "llvm":["taskset","-c","18",rustc,*common,"-o",f"{work}/e_llvm",f"{work}/empty.rs"],
 "tcg" :["taskset","-c","18",rustc,f"-Zcodegen-backend={dylib}",*common,"-o",f"{work}/e_tcg",f"{work}/empty.rs"],
}
res={k:[] for k in lanes}
for i in range(n+1):                       # +1 warmup round, discarded
    for k,argv in lanes.items():
        t0=time.perf_counter()
        r=subprocess.run(argv,capture_output=True,text=True)
        dt=(time.perf_counter()-t0)*1000
        if r.returncode!=0:
            sys.stderr.write(r.stderr[-3000:]); sys.exit(1)
        if i: res[k].append(dt)
for k in res: res[k].sort()
l,t=res["llvm"],res["tcg"]
print(f"{l[0]:.1f} {l[len(l)//2]:.1f} {t[0]:.1f} {t[len(t)//2]:.1f} {t[0]-l[0]:+.1f} {t[len(t)//2]-l[len(l)//2]:+.1f}")
PY
)
read LMIN LMED TMIN TMED DMIN DMED <<<"$RUSTC_T"

# ---- static facts ----
read SZ TEXT REL DYNDEF <<<"$(python3 - "$DYLIB" <<'PY'
import subprocess,re,sys,os
so=sys.argv[1]
s=subprocess.run(["readelf","-SW",so],capture_output=True,text=True).stdout
sec={}
for line in s.splitlines():
    m=re.match(r'\s*\[\s*\d+\]\s+(\S+)\s+(\S+)\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)',line)
    if m: sec[m.group(1)]=int(m.group(5),16)
r=subprocess.run(["readelf","-rW",so],capture_output=True,text=True).stdout
nrel=sum(1 for l in r.splitlines() if "R_AARCH64" in l)
d=subprocess.run(["readelf","--dyn-syms","-W",so],capture_output=True,text=True).stdout
ndef=sum(1 for l in d.splitlines()[3:] if len(l.split())>7 and l.split()[6]!="UND")
print(os.path.getsize(so), sec.get(".text",0), nrel, ndef)
PY
)"

printf '%s\n' "=============================================================="
printf '%s\n' "$LABEL"
printf '  dylib     : %s\n' "$DYLIB"
printf '  size      : %.2f MB   .text %.2f MB\n' "$(bc -l <<<"$SZ/1048576")" "$(bc -l <<<"$TEXT/1048576")"
printf '  relocs    : %s   exported dynsyms: %s\n' "$REL" "$DYNDEF"
printf '  %s\n' "$DL"
printf '  LOAD COST : %s ms median paired diff (q1 %s)  [metadata-only base %s ms]\n' "$MLOAD" "$MLOADQ1" "$MOFF"
printf '  rustc ms  : llvm min %s med %s | tcg min %s med %s\n' "$LMIN" "$LMED" "$TMIN" "$TMED"
printf '  DEFICIT   : min %s ms   med %s ms\n' "$DMIN" "$DMED"
