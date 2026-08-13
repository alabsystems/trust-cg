#!/usr/bin/env bash
# Pareto-curve comparison: trust-cg vs LLVM across the FULL opt-level range.
#
# WHY THIS EXISTS
#
# `run_bench_pinned.sh` compares one point on each curve (-Copt-level=3 both
# lanes). That answers "is trust-cg -O3 better than LLVM -O3", which is NOT the
# question that decides whether trust-cg can replace LLVM.
#
# Compilers do not offer a single operating point. They offer a CURVE: spend
# more compile time, get faster code. LLVM's cheap end (-O0) is very cheap
# because it uses a fast register allocator and skips most passes; its expensive
# end (-O3) is slow but produces the fastest code.
#
# The replacement criterion is PARETO DOMINANCE of the whole curve:
#
#   for every operating point LLVM offers at (compile_time, run_time),
#   trust-cg offers some point with compile_time' <= compile_time
#                                and run_time'     <= run_time
#
# Under that criterion trust-cg -O3 does NOT need to out-compile LLVM -O3. It
# needs to reach LLVM's runtime at less compile cost, at SOME setting. A single
# O3-vs-O3 ratio can look like a loss while the curve still dominates -- and can
# look like a win while the curve does not.
#
# This harness measures the whole matrix so the claim is decided by the frontier
# rather than by one point.
#
# Timing methodology is inherited from run_bench_pinned.sh: heterogeneous cores
# on this class of host give a ~1.4x spread by scheduler luck, so both lanes are
# pinned to the SAME core and every figure is min-of-N.
#
# Author: Andrew Yates · Copyright 2026 Andrew Yates · License: Apache-2.0
set -u

PROGS="${PROGS:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../benchmarks/beat-llvm/progs" && pwd)}"
DYLIB="${DYLIB:?set DYLIB to librustc_codegen_trust_cg.so}"
TOOLCHAIN="${TOOLCHAIN:-nightly-2026-04-20}"
# Resolve rustc ONCE. `rustup run` re-execs a shim per invocation, and that shim
# cost lands asymmetrically on the two lanes -- measured on an empty program it
# inflated the trust-cg deficit from 5.3ms to 11.9ms, i.e. it more than doubled
# the very quantity this harness exists to measure.
RUSTC_BIN="${RUSTC_BIN:-$(rustup which --toolchain "$TOOLCHAIN" rustc)}"
LEVELS="${LEVELS:-0 1 2 3}"
CREPS="${CREPS:-3}"   # compile repetitions (min-of)
RREPS="${RREPS:-5}"   # runtime repetitions (min-of)
OUT="${OUT:-curve_results.csv}"

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
# Skip cores that already have a busy process. Pinning onto an occupied core
# silently halves throughput, and because BOTH lanes share the core the ratio
# survives while every absolute number is inflated -- which is exactly the kind
# of corruption that looks like a clean result. Measured on this host: a compile
# that takes 74ms on an idle big core reads 110ms on a little one, and worse on
# a contended one.
core_busy() {
    ps -eo psr,pcpu --no-headers 2>/dev/null | awk -v c="$1" '$1==c && $2>50 {f=1} END{exit !f}'
}
pick_idle_core() {
    local best_cpu="" best_cap=0 cap
    for d in /sys/devices/system/cpu/cpu[0-9]*; do
        [ -r "$d/cpu_capacity" ] || continue
        local n; n=$(basename "$d" | tr -dc '0-9')
        core_busy "$n" && continue
        cap=$(cat "$d/cpu_capacity")
        if [ "$cap" -gt "$best_cap" ]; then best_cap=$cap; best_cpu=$n; fi
    done
    echo "$best_cpu"
}
if [ -z "${CORE:-}" ]; then
    CORE="$(pick_idle_core)"
    if [ -z "$CORE" ]; then
        CORE="$(pick_core)"
        echo "run_curve: WARNING every core is busy — pinned to $CORE anyway, numbers are contended" >&2
    fi
elif core_busy "$CORE"; then
    echo "run_curve: WARNING requested core $CORE is >50% busy — results will be inflated" >&2
fi

if ! command -v taskset >/dev/null; then
    echo "run_curve: taskset not found — refusing to report unpinned numbers" >&2
    exit 2
fi

# SOLVER PRESENCE. Whether the refinement lanes actually solve depends on
# whether an `ay` binary happens to be built on the host -- and it swings
# trust-cg compile time by ~23x (302ms vs 13ms on the same heap compiles). A
# previously-circulated compile figure was contaminated exactly this way. It is
# never acceptable to report a compile number without stating this, so record it
# in the CSV rather than trusting anyone to remember.
SOLVER_PRESENT=no
for cand in "$HOME/ay/target/release/ay" "$HOME/ay/target/debug/ay"; do
    [ -x "$cand" ] && SOLVER_PRESENT=yes
done
# Default to the apples-to-apples configuration: LLVM runs no solver, so neither
# should trust-cg when comparing pure codegen. Set TCG_SOLVER=1 to measure the
# solver-on product instead.
#
# HEADLINE ELIGIBILITY. `benchmarks/beat-llvm/run.py` already defines the
# project standard: a run is NOT headline-eligible if TCG_NO_PROOF_CERTS,
# TCG_REFINE_SOLVER=0, or TCG_NO_PROOF_CACHE is in the trust-cg environment
# ("weakening"). Those switches make trust-cg skip work that the shipping
# product does, so a comparison using them measures a configuration nobody can
# ship. This harness applies the SAME rule rather than inventing a laxer one,
# and stamps the verdict into the CSV so a number cannot be quoted as headline
# later by someone who did not watch it run.
#
# TCG_STRICT=1 runs the shippable configuration: proof certs on, solver in
# whatever state the host actually provides.
STRICT="${TCG_STRICT:-0}"
if [ "$STRICT" = "1" ]; then
    SOLVER_MODE=host
    TCG_ENV=()
    WEAKENING=no
elif [ "${TCG_SOLVER:-0}" = "1" ]; then
    SOLVER_MODE=on
    TCG_ENV=(TCG_NO_PROOF_CERTS=1)
    WEAKENING=yes
else
    SOLVER_MODE=off
    TCG_ENV=(TCG_NO_PROOF_CERTS=1 TCG_REFINE_SOLVER=0)
    WEAKENING=yes
fi

load=$(cut -d' ' -f1 /proc/loadavg)
echo "core=$CORE levels='$LEVELS' creps=$CREPS rreps=$RREPS loadavg=$load" >&2
ELIGIBLE=yes; REASONS=""
[ "$WEAKENING" = yes ] && { ELIGIBLE=no; REASONS="proof-weakening env (${TCG_ENV[*]})"; }
awk -v l="$load" 'BEGIN{ exit !(l+0 > 2.0) }' && { ELIGIBLE=no; REASONS="$REASONS${REASONS:+; }loadavg $load > 2.0"; }
git -C "$(dirname "${BASH_SOURCE[0]}")" diff --quiet 2>/dev/null || { ELIGIBLE=no; REASONS="$REASONS${REASONS:+; }git tree dirty"; }
echo "solver_binary_on_host=$SOLVER_PRESENT solver_mode=$SOLVER_MODE weakening=$WEAKENING" >&2
echo "HEADLINE_ELIGIBLE=$ELIGIBLE${REASONS:+  (${REASONS})}" >&2
[ "$ELIGIBLE" = no ] && echo "run_curve: these numbers are DIAGNOSTIC ONLY — do not quote them as headline results" >&2
if [ "$SOLVER_PRESENT" = yes ] && [ "$SOLVER_MODE" = off ]; then
    echo "run_curve: NOTE ay is built on this host; relying on TCG_REFINE_SOLVER=0 to gate it." >&2
fi
awk -v l="$load" 'BEGIN{ if (l+0 > 2.0) print "run_curve: WARNING loadavg " l " > 2.0 — results are advisory, not headline evidence" > "/dev/stderr" }'

now() { python3 -c "import time;print(time.perf_counter())"; }

# min-of-N wall time for an arbitrary pinned command; prints "ms exit"
best_cmd() {
    local reps="$1"; shift
    local best="" rc=0 t0 t1 d
    for _ in $(seq "$reps"); do
        t0=$(now); taskset -c "$CORE" "$@" >/dev/null 2>&1; rc=$?; t1=$(now)
        d=$(python3 -c "print(($t1-$t0)*1000)")
        best=$(python3 -c "print(min(float('${best:-1e9}'), $d))")
    done
    echo "$best $rc"
}

echo "# solver_binary_on_host=$SOLVER_PRESENT solver_mode=$SOLVER_MODE weakening=$WEAKENING headline_eligible=$ELIGIBLE reasons=${REASONS:-none} core=$CORE creps=$CREPS rreps=$RREPS" > "$OUT"
echo "bench,level,lane,compile_ms,run_ms,exit" >> "$OUT"
for f in "$PROGS"/*.rs; do
    n=$(basename "$f" .rs)
    for lvl in $LEVELS; do
        # ---- LLVM lane ----
        b="cv_l_${n}_O${lvl}"; rm -f "$b"
        read -r cms _ <<< "$(best_cmd "$CREPS" "$RUSTC_BIN" \
            --edition 2021 "-Copt-level=$lvl" -Cpanic=abort -Coverflow-checks=off \
            -Ccodegen-units=1 -o "$b" "$f")"
        if [ -x "$b" ]; then
            read -r rms rrc <<< "$(best_cmd "$RREPS" "./$b")"
        else
            rms=""; rrc="BUILD_FAIL"
        fi
        printf "%s,%s,llvm,%s,%s,%s\n" "$n" "$lvl" "$cms" "$rms" "$rrc" >> "$OUT"

        # ---- trust-cg lane ----
        b="cv_t_${n}_O${lvl}"; rm -f "$b"
        # `env` rather than a function-call prefix: POSIX leaves the persistence
        # of `VAR=x func` unspecified, and a leaked TCG_NO_PROOF_CERTS would
        # silently disable proof work in the LLVM-lane loop iteration too.
        read -r cms _ <<< "$(best_cmd "$CREPS" env "${TCG_ENV[@]}" "$RUSTC_BIN" \
            "-Zcodegen-backend=$DYLIB" --edition 2021 "-Copt-level=$lvl" -Cpanic=abort \
            -Coverflow-checks=off -Ccodegen-units=1 -o "$b" "$f")"
        if [ -x "$b" ]; then
            read -r rms rrc <<< "$(best_cmd "$RREPS" "./$b")"
        else
            rms=""; rrc="BUILD_FAIL"
        fi
        printf "%s,%s,tcg,%s,%s,%s\n" "$n" "$lvl" "$cms" "$rms" "$rrc" >> "$OUT"
        printf "  %-20s O%s done\n" "$n" "$lvl" >&2
    done
done

python3 - "$OUT" <<'PY'
import csv, sys, collections

lines = [l for l in open(sys.argv[1]) if not l.startswith("#")]
rows = list(csv.DictReader(lines))
pts = collections.defaultdict(dict)   # bench -> (lane, level) -> (compile, run)
# INTENT-TO-TREAT: count every cell we attempted, and report what was dropped.
# Silently filtering unusable rows out of the denominator turns a partial result
# into a clean-looking one; a dropped BUILD_FAIL is a LOSS, not an absence.
attempted = len(rows)
dropped = []
for r in rows:
    if not r["compile_ms"] or not r["run_ms"]:
        dropped.append(f'{r["bench"]}/O{r["level"]}/{r["lane"]}:{r["exit"] or "no-timing"}')
        continue
    try:
        pts[r["bench"]][(r["lane"], r["level"])] = (float(r["compile_ms"]), float(r["run_ms"]))
    except ValueError:
        dropped.append(f'{r["bench"]}/O{r["level"]}/{r["lane"]}:unparseable')
        continue

# Classify each non-dominating program by WHY it fails, because the two causes
# need completely different work:
#   compile-only  -- some trust-cg point already matches LLVM's runtime, it just
#                    costs too much to compile. Fixable in the backend's speed.
#   runtime-blocked -- NO trust-cg point reaches that runtime at any setting.
#                    Needs codegen quality, not compile speed.
# Do not collapse these. An earlier ad-hoc version of this analysis computed the
# compile deficit as a max over only the points whose runtime was reachable,
# which silently dropped every runtime-blocked point and reported programs like
# p4_matmul (best tcg r=93 vs LLVM r=48) as needing nothing but compile time.
dominated, not_dominated, incomplete = [], [], []
compile_only, runtime_blocked = [], []
for bench, d in sorted(pts.items()):
    llvm = [(lv, v) for (lane, lv), v in d.items() if lane == "llvm"]
    tcg  = [v for (lane, _), v in d.items() if lane == "tcg"]
    if not llvm or not tcg:
        incomplete.append(bench); continue
    misses = []
    for lv, (lc, lr) in sorted(llvm):
        if not any(tc <= lc and tr <= lr for (tc, tr) in tcg):
            best = min(tcg, key=lambda p: p[1])
            misses.append(f"O{lv}(c={lc:.0f},r={lr:.0f}) best-tcg(c={best[0]:.0f},r={best[1]:.0f})")
    (not_dominated if misses else dominated).append((bench, misses))
    if not misses:
        continue
    best_rt = min(t[1] for t in tcg)
    unmatched = [(lc, lr) for lv, (lc, lr) in sorted(llvm)
                 if not any(tc <= lc and tr <= lr for (tc, tr) in tcg)]
    blocked = [(lc, lr) for lc, lr in unmatched if best_rt > lr]
    if blocked:
        want = min(lr for _, lr in blocked)
        runtime_blocked.append((best_rt / want if want else float("inf"), bench, best_rt, want))
    else:
        need = max(min(tc for tc, tr in tcg if tr <= lr) - lc for lc, lr in unmatched)
        compile_only.append((need, bench))

print(f"\n=== PARETO DOMINANCE (trust-cg curve vs LLVM curve) ===")
print(f"DOMINATES LLVM's whole curve : {len(dominated)}/{len(dominated)+len(not_dominated)}")
for b, _ in dominated:
    print(f"  OK   {b}")
for b, misses in not_dominated:
    print(f"  MISS {b}")
    for m in misses:
        print(f"         unmatched LLVM point: {m}")
if incomplete:
    print("INCOMPLETE (missing lane/level):", ", ".join(incomplete))
print(f"\nCOMPILE-ONLY deficit ({len(compile_only)}) — runtime already sufficient:")
for need, bench in sorted(compile_only):
    print(f"  {bench:22s} shave {need:6.1f}ms")
print(f"RUNTIME-BLOCKED ({len(runtime_blocked)}) — no trust-cg point reaches LLVM's runtime:")
for ratio, bench, got, want in sorted(runtime_blocked, reverse=True):
    floor = "  (within measurement floor)" if ratio < 1.10 else ""
    print(f"  {bench:22s} best tcg r={got:7.0f} vs LLVM r={want:7.0f}  ({ratio:.2f}x){floor}")

usable = attempted - len(dropped)
print(f"\nCOVERAGE {usable}/{attempted} cells usable ({100.0*usable/attempted:.1f}%)" if attempted else "COVERAGE n/a")
if dropped:
    print(f"DROPPED {len(dropped)} cell(s) — each is a FAILURE, not an absence:")
    for d in dropped:
        print(f"  {d}")
PY
