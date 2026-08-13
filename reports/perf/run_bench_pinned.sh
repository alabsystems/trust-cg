#!/usr/bin/env bash
# Low-noise aarch64 runtime comparison: trust-cg bridge vs LLVM.
#
# WHY THIS EXISTS
#
# `run_bench.sh` hardcodes `x86_64-apple-darwin` and a `.dylib`, so it cannot run
# on aarch64 Linux at all. More importantly, naive timing on this class of host
# cannot resolve the differences that matter. Measured, same binary, 8 runs,
# unpinned:
#
#     tcg : 329.7 318.4 324.9 324.3 333.5 325.0 328.5 327.2
#     llvm: 319.2 329.7 331.3 333.8 335.4 324.3 333.0 324.2
#
# The distributions overlap almost entirely — roughly 5% spread, which silently
# swallows any sub-10% change and produces phantom wins and losses.
#
# Two causes, both fixed here:
#
#   1. HETEROGENEOUS CORES. This is a big.LITTLE-class part (Cortex-X925 +
#      Cortex-A725). `/sys/devices/system/cpu/cpuN/cpu_capacity` reports 718 for
#      the little cores and up to 1024 for the big ones — a ~1.4x spread decided
#      purely by which core the scheduler happened to pick. Pinning removes it.
#   2. TOO FEW REPETITIONS. min-of-3 on a loaded box is dominated by scheduling
#      noise. min-of-N with N>=7 on a pinned core tightens it to ~1.7%.
#
# Both lanes are pinned to the SAME core, so the comparison stays honest even
# when that core is not the fastest one available.
#
# Author: Andrew Yates · Copyright 2026 Andrew Yates · License: Apache-2.0
set -u

PROGS="${PROGS:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../benchmarks/beat-llvm/progs" && pwd)}"
DYLIB="${DYLIB:?set DYLIB to librustc_codegen_trust_cg.so}"
TOOLCHAIN="${TOOLCHAIN:-nightly-2026-04-20}"
REPS="${REPS:-7}"
OUT="${OUT:-pinned_results.csv}"

# Pick the highest-capacity core unless the caller names one. Consistency
# matters more than absolute speed, but a big core is more representative of
# the workloads this backend targets.
pick_core() {
    local best_cpu=0 best_cap=0 cap
    for d in /sys/devices/system/cpu/cpu[0-9]*; do
        [ -r "$d/cpu_capacity" ] || continue
        cap=$(cat "$d/cpu_capacity")
        if [ "$cap" -gt "$best_cap" ]; then
            best_cap=$cap
            best_cpu=$(basename "$d" | tr -dc '0-9')
        fi
    done
    echo "$best_cpu"
}
CORE="${CORE:-$(pick_core)}"

if ! command -v taskset >/dev/null; then
    echo "run_bench_pinned: taskset not found — refusing to report unpinned numbers" >&2
    exit 2
fi

load=$(cut -d' ' -f1 /proc/loadavg)
echo "core=$CORE reps=$REPS loadavg=$load" >&2
awk -v l="$load" 'BEGIN{ if (l+0 > 2.0) print "run_bench_pinned: WARNING loadavg " l " > 2.0 — results are advisory, not headline evidence" > "/dev/stderr" }'

now() { python3 -c "import time;print(time.perf_counter())"; }

best_of() { # $1=binary -> prints "ms exit"
    local best="" rc=0 t0 t1 d
    for _ in $(seq "$REPS"); do
        t0=$(now); taskset -c "$CORE" "$1" >/dev/null 2>&1; rc=$?; t1=$(now)
        d=$(python3 -c "print(($t1-$t0)*1000)")
        best=$(python3 -c "print(min(float('${best:-1e9}'), $d))")
    done
    echo "$best $rc"
}

echo "bench,llvm_ms,tcg_ms,ratio,llvm_exit,tcg_exit,match" > "$OUT"
for f in "$PROGS"/*.rs; do
    n=$(basename "$f" .rs)
    rm -f "bp_l_$n" "bp_t_$n"
    rustup run "$TOOLCHAIN" rustc --edition 2021 -Copt-level=3 -Cpanic=abort \
        -Coverflow-checks=off -Ccodegen-units=1 -o "bp_l_$n" "$f" >/dev/null 2>&1
    TCG_NO_PROOF_CERTS=1 rustup run "$TOOLCHAIN" rustc -Zcodegen-backend="$DYLIB" \
        --edition 2021 -Copt-level=3 -Cpanic=abort -Coverflow-checks=off \
        -Ccodegen-units=1 -o "bp_t_$n" "$f" >/dev/null 2>&1
    if [ ! -x "bp_l_$n" ] || [ ! -x "bp_t_$n" ]; then
        echo "$n,,,,,,BUILD_FAIL" >> "$OUT"; continue
    fi
    read -r lms lrc <<< "$(best_of "./bp_l_$n")"
    read -r tms trc <<< "$(best_of "./bp_t_$n")"
    m=NO; [ "$lrc" = "$trc" ] && m=YES
    r=$(python3 -c "print(f'{$tms/$lms:.3f}')")
    printf "%s,%.1f,%.1f,%s,%s,%s,%s\n" "$n" "$lms" "$tms" "$r" "$lrc" "$trc" "$m" >> "$OUT"
    printf "  %-22s llvm=%7.1fms tcg=%7.1fms  %sx  %s\n" "$n" "$lms" "$tms" "$r" "$m" >&2
done

python3 - "$OUT" <<'PY'
import csv, math, sys
rows = [r for r in csv.DictReader(open(sys.argv[1])) if r["ratio"]]
bad = [r["bench"] for r in rows if r["match"] != "YES"]
ok = [r for r in rows if r["match"] == "YES"]
rs = [float(r["ratio"]) for r in ok]
gm = math.exp(sum(map(math.log, rs)) / len(rs))
print(f"\nRUNTIME geomean {gm:.3f}x  (n={len(rs)}, wins {sum(1 for v in rs if v<1.0)}/{len(rs)})")
print("MISMATCH:", bad or "none — every checksum matches LLVM")
PY
