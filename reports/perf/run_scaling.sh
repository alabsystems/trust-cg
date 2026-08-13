#!/usr/bin/env bash
# Compile-time SCALING: trust-cg vs LLVM as function size grows.
#
# WHY THIS EXISTS
#
# `run_bench_pinned.sh` and `run_curve.sh` both measure the beat-llvm corpus,
# whose largest program is ~30 lines. That corpus is structurally blind to
# superlinear backend behaviour: three separate O(n^2) sites hid behind a
# healthy-looking 1.06x geomean until this harness existed.
#
# The question here is NOT "what is the ratio" but "does the ratio GROW". A
# constant ratio is ordinary constant-factor work; a climbing one is an
# algorithmic defect and is worth orders of magnitude more attention.
#
# METHOD
#
# * `--emit=obj`: excludes the linker, which is the same external `ld` for both
#   lanes and would otherwise dominate and mask the codegen difference.
# * Resolved rustc, not `rustup run` — its shim cost lands asymmetrically and
#   more than doubled a measured deficit once already.
# * Both lanes pinned to the SAME core: this class of host is big.LITTLE and
#   scheduler luck alone gives a ~1.4x spread.
# * min-of-N, and the RATIO PER SIZE is what gets reported, because that is the
#   quantity the question is about.
# * Every build is checked for an actual object. A backend that fails closed
#   produces no output very quickly, and an unchecked timer reads that as a fast
#   compile — this harness has caught exactly that mistake.
#
# Author: Andrew Yates · Copyright 2026 Andrew Yates · License: Apache-2.0
set -u

GEN="${GEN:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../benchmarks/scaling" && pwd)/gen.py}"
DYLIB="${DYLIB:?set DYLIB to librustc_codegen_trust_cg.so}"
TOOLCHAIN="${TOOLCHAIN:-nightly-2026-04-20}"
RUSTC_BIN="${RUSTC_BIN:-$(rustup which --toolchain "$TOOLCHAIN" rustc)}"
SHAPES="${SHAPES:-mul_chain ilp_add branchy many_fns array_loop}"
SIZES="${SIZES:-200 400 800 1600}"
REPS="${REPS:-3}"
OPT="${OPT:-3}"
OUT="${OUT:-scaling_results.csv}"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

pick_core() {
    local best_cpu=0 best_cap=0 cap
    for d in /sys/devices/system/cpu/cpu[0-9]*; do
        [ -r "$d/cpu_capacity" ] || continue
        cap=$(cat "$d/cpu_capacity")
        if [ "$cap" -gt "$best_cap" ]; then best_cap=$cap; best_cpu=$(basename "$d" | tr -dc '0-9'); fi
    done
    echo "$best_cpu"
}
CORE="${CORE:-$(pick_core)}"

# min-of-REPS wall time in microseconds; prints "us ok|FAIL".
best_compile() {
    local outdir="$1"; shift
    local best=99999999 i s e us produced
    for i in $(seq 1 "$REPS"); do
        rm -rf "$outdir"; mkdir -p "$outdir"
        s=$(date +%s%N)
        ( cd "$outdir" && "$@" >/dev/null 2>&1 )
        e=$(date +%s%N)
        us=$(( (e - s) / 1000 ))
        [ "$us" -lt "$best" ] && best=$us
    done
    # Count ANY artifact, not `*.o`: the two lanes name their output
    # differently under `--emit=obj -o out` — LLVM writes a single `out`, while
    # trust-cg writes one `out.<cgu>.rcgu.o` per codegen unit. Globbing `*.o`
    # therefore reported every LLVM build as a failure.
    produced=$(find "$outdir" -type f 2>/dev/null | wc -l)
    if [ "$produced" -eq 0 ]; then echo "$best FAIL"; else echo "$best ok"; fi
}

echo "# core=$CORE reps=$REPS opt=$OPT emit=obj rustc=$RUSTC_BIN" > "$OUT"
echo "shape,n,llvm_us,tcg_us,ratio,status" >> "$OUT"

for shape in $SHAPES; do
    prev_ratio=""
    for n in $SIZES; do
        src="$WORK/${shape}_${n}.rs"
        python3 "$GEN" "$shape" "$n" "$src" || { echo "gen failed: $shape $n" >&2; continue; }

        read -r lus lok <<< "$(best_compile "$WORK/l" taskset -c "$CORE" "$RUSTC_BIN" \
            --edition 2021 "-Copt-level=$OPT" -Cpanic=abort -Coverflow-checks=off \
            -Ccodegen-units=1 --emit=obj -o out "$src")"
        read -r tus tok <<< "$(best_compile "$WORK/t" env TCG_NO_PROOF_CERTS=1 TCG_REFINE_SOLVER=0 \
            taskset -c "$CORE" "$RUSTC_BIN" "-Zcodegen-backend=$DYLIB" \
            --edition 2021 "-Copt-level=$OPT" -Cpanic=abort -Coverflow-checks=off \
            -Ccodegen-units=1 --emit=obj -o out "$src")"

        status="ok"
        [ "$lok" = FAIL ] && status="llvm_build_fail"
        [ "$tok" = FAIL ] && status="tcg_build_fail"
        ratio=$(python3 -c "print(f'{$tus/$lus:.3f}')" 2>/dev/null || echo "")
        printf "%s,%s,%s,%s,%s,%s\n" "$shape" "$n" "$lus" "$tus" "$ratio" "$status" >> "$OUT"
        printf "  %-11s n=%-6s llvm=%7.1fms tcg=%7.1fms  %sx  %s\n" \
            "$shape" "$n" \
            "$(python3 -c "print($lus/1000)")" "$(python3 -c "print($tus/1000)")" \
            "$ratio" "$status" >&2
        prev_ratio="$ratio"
    done
done

python3 - "$OUT" <<'PY'
import csv, sys
rows = [r for r in csv.DictReader(l for l in open(sys.argv[1]) if not l.startswith('#'))]
print("\n=== SCALING VERDICT (does the ratio grow with N?) ===")
bad = 0
for shape in dict.fromkeys(r['shape'] for r in rows):
    rs = [r for r in rows if r['shape'] == shape and r['status'] == 'ok' and r['ratio']]
    if len(rs) < 2:
        print(f"  {shape:12s} insufficient data"); continue
    first, last = float(rs[0]['ratio']), float(rs[-1]['ratio'])
    n0, n1 = rs[0]['n'], rs[-1]['n']
    growth = last / first
    # A ratio that grows faster than ~1.5x across the size sweep is the
    # signature of a superlinear term, not constant-factor noise.
    verdict = "FLAT (good)" if growth < 1.5 else "GROWING <-- superlinear"
    if growth >= 1.5: bad += 1
    print(f"  {shape:12s} n={n0}->{n1}: {first:.2f}x -> {last:.2f}x  (x{growth:.2f})  {verdict}")
fails = [r for r in rows if r['status'] != 'ok']
if fails:
    print(f"\n  {len(fails)} BUILD FAILURES (not counted as fast compiles):")
    for r in fails: print(f"    {r['shape']} n={r['n']} {r['status']}")
print(f"\n  {bad} shape(s) show superlinear growth.")
PY
