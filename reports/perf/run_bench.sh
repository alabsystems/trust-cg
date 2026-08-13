#!/usr/bin/env bash
# GOAL-3 PERFORMANCE BASELINE harness.
#
# Measures trust-cg's x86 backend (the bridge) vs LLVM (rustc default backend)
# on BOTH compile time and execution time, for a suite of small-but-nontrivial
# deterministic compute benchmarks. MEASUREMENT ONLY — does not modify the
# compiler.
#
# For each benchmark it builds four object files:
#   - LLVM at -Copt-level=1   (matches the bridge's pinned O1, for fair compare)
#   - LLVM at -Copt-level=3   (LLVM's best, for context / the real gap)
#   - BRIDGE  (proofs ON  — the default, TCG_NO_PROOF_CERTS unset)
#   - BRIDGE  (proofs OFF — TCG_NO_PROOF_CERTS=1, to isolate gate overhead)
# All builds use -Coverflow-checks=off -Ccodegen-units=1 -Cpanic=abort.
#
# COMPILE TIME: best-of-3 warm wall clock of the rustc invocation (object only,
#   no link), per variant.
# EXEC TIME:    each object is linked with `cc` (+ abort stubs for any undefined
#   panic_* symbols, mirroring the in-tree x86 tests) into a native Mach-O
#   binary; the binary is run best-of-5; the program self-iterates its kernel to
#   run ~0.1-1s so the timing is meaningful. The process EXIT CODE is the kernel
#   checksum (& 0xff) — we assert the bridge binary yields the SAME code as LLVM.
#   A mismatch is a CORRECTNESS bug, NOT a perf result.
#
# Output: a CSV (results.csv) consumed by the report generator. Benchmarks the
# bridge fails to compile (fail-closed coverage gaps) are recorded with a FAIL
# marker and excluded from perf stats.
#
# Author: Andrew Yates · Copyright 2026 Andrew Yates · License: Apache-2.0
set -u

# ---- configuration ------------------------------------------------------------
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCH_DIR="${BENCH_DIR:-$HERE/benches}"   # override for a subset smoke test
WORKTREE="$(cd "$HERE/../.." && pwd)"
TARGET="x86_64-apple-darwin"
TOOLCHAIN="nightly-2026-04-20"

# The bridge dylib. Allow override via $DYLIB; else default to the standard
# release path under the worktree's target-bridge dir.
DYLIB="${DYLIB:-$WORKTREE/target-bridge/release/librustc_codegen_trust_cg.dylib}"

COMPILE_REPS=3          # best-of-N LLVM compile timing (fast, so 3)
BRIDGE_COMPILE_REPS=1   # bridge compile timing. The proof-gated compile is
                        # CPU-bound, deterministic, and can take 1-3 MINUTES on
                        # loop/array-heavy kernels (the proof DB discharges one
                        # obligation per emitted instruction); best-of-1 is a
                        # stable floor and keeps the suite tractable. Bump for a
                        # tighter compile-time estimate if you have the time.
EXEC_REPS=5             # best-of-N exec timing

OUT_CSV="${OUT_CSV:-$HERE/results.csv}"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

# ---- helpers ------------------------------------------------------------------

# Timing is delegated to timeit.py (one python process per measurement, so
# interpreter startup is amortized over all reps — a per-run python spawn would
# dwarf a sub-100ms kernel). It reports best-of-N min and the child exit code:
#   - "wall" mode for COMPILE (user-visible rustc latency)
#   - "cpu"  mode for EXEC (child user+sys CPU; immune to system-load noise)
TIMEIT="$HERE/timeit.py"

# RC handoff: time_wall/time_cpu run inside a $(...) command substitution, so a
# plain shell-var assignment there would not reach the caller. They instead
# write the child RC to $RCFILE, which the caller reads into LAST_RC/EXIT_CODE.
RCFILE=""
LAST_RC=0
ERRFILE=""
time_wall() {
    local reps="$1"; shift
    local out ms rc
    if [[ -n "$ERRFILE" ]]; then
        out="$(python3 "$TIMEIT" wall "$reps" --errfile "$ERRFILE" -- "$@")"
    else
        out="$(python3 "$TIMEIT" wall "$reps" -- "$@")"
    fi
    ms="$(printf '%s\n' "$out" | sed -n 's/^MS=//p')"
    rc="$(printf '%s\n' "$out" | sed -n 's/^RC=//p')"
    [[ -n "$RCFILE" ]] && printf '%s' "$rc" > "$RCFILE"
    echo "$ms"
}

# time_cpu <reps> <cmd...>: echo min CPU ms (best-of-reps). Writes RC to $RCFILE.
EXIT_CODE=0
time_cpu() {
    local reps="$1"; shift
    local out ms rc
    out="$(python3 "$TIMEIT" cpu "$reps" -- "$@")"
    ms="$(printf '%s\n' "$out" | sed -n 's/^MS=//p')"
    rc="$(printf '%s\n' "$out" | sed -n 's/^RC=//p')"
    [[ -n "$RCFILE" ]] && printf '%s' "$rc" > "$RCFILE"
    echo "$ms"
}

# llvm_cmd / bridge_cmd build the rustc argv into the global CMD array (so the
# exact same argv can be both run once for a status check AND handed to
# timeit.py for timing — timeit.py execs a real binary, it cannot call a shell
# function).
#
# IMPORTANT object-emission asymmetry: with `--emit=obj -o <dir>/stem.o`,
#   - LLVM emits exactly <dir>/stem.o (one file).
#   - the BRIDGE emits one object PER codegen unit, named <dir>/stem.<cgu>.rcgu.o
#     (e.g. main.rcgu.o + a separate object per monomorphized core intrinsic
#     like wrapping_add), and does NOT create stem.o itself.
# So each variant emits into its OWN clean directory and we link ALL *.o in it.

# llvm_cmd <src> <outdir> <optlevel>: rustc, default (LLVM) backend.
llvm_cmd() {
    local src="$1" outdir="$2" opt="$3"
    CMD=(rustup run "$TOOLCHAIN" rustc --edition=2021 --crate-type bin
         --target "$TARGET" -Cpanic=abort -Coverflow-checks=off
         -Ccodegen-units=1 -Copt-level="$opt"
         --emit=obj -o "$outdir/o.o" "$src")
}

# bridge_cmd <src> <outdir>: rustc with -Zcodegen-backend=$DYLIB.
# Honors env TCG_NO_PROOF_CERTS (set by the caller) for proofs on/off.
# BRIDGE_OPT_LEVEL (default 3): the bridge's machine-opt passes (vectorizer,
# x86_licm, SROA, pure-call hoist, ...) fire at O2/O3 only — the historical
# no-flag invocation compiled at rustc's default O0 and measured NONE of them
# (the "pinned O1" premise in the header predates raising the machine-opt cap).
bridge_cmd() {
    local src="$1" outdir="$2"
    CMD=(rustup run "$TOOLCHAIN" rustc --edition=2021 --crate-type bin
         -Zcodegen-backend="$DYLIB"
         --target "$TARGET" -Cpanic=abort -Coverflow-checks=off
         -Ccodegen-units=1 -Copt-level="${BRIDGE_OPT_LEVEL:-3}"
         --emit=obj -o "$outdir/o.o" "$src")
}

# link_dir <objdir> <bin>: link ALL *.o in objdir into a runnable Mach-O,
# supplying abort stubs for any undefined panic_* symbols (these never fire at
# the chosen inputs). Returns nonzero on link failure or if no objects exist.
link_dir() {
    local objdir="$1" bin="$2"
    local objs=("$objdir"/*.o)
    [[ -e "${objs[0]}" ]] || return 1
    local stubs="$objdir/stubs.c"
    {
        echo '#include <stdlib.h>'
        nm -u "${objs[@]}" 2>/dev/null | while read -r line; do
            sym="${line#U}"; sym="${sym// /}"
            case "$sym" in
                *panic*)
                    c="${sym#_}"
                    echo "void ${c}(void) __asm__(\"${sym}\"); void ${c}(void){ abort(); }"
                    ;;
            esac
        done
    } > "$stubs"
    cc -o "$bin" "${objs[@]}" "$stubs" 2>/dev/null
}

# ---- preflight ----------------------------------------------------------------
echo "GOAL-3 perf baseline harness" >&2
echo "  worktree : $WORKTREE" >&2
echo "  dylib    : $DYLIB" >&2
echo "  target   : $TARGET  (host arch: $(uname -m))" >&2
echo "  toolchain: $TOOLCHAIN" >&2

if [[ ! -f "$DYLIB" ]]; then
    echo "FATAL: bridge dylib not found at $DYLIB" >&2
    echo "Build it first (see reports/perf/baseline_*.md header)." >&2
    exit 1
fi

# CSV header
echo "bench,llvm_o1_compile_ms,llvm_o3_compile_ms,bridge_compile_ms,bridge_noproof_compile_ms,llvm_o1_exec_ms,llvm_o3_exec_ms,bridge_exec_ms,llvm_checksum,bridge_checksum,checksum_match,bridge_status" > "$OUT_CSV"

RCFILE="$SCRATCH/rc"   # RC handoff out of the $(...) timing subshells
# rc_last: echo the RC the last time_wall/time_cpu wrote to $RCFILE.
rc_last() { cat "$RCFILE" 2>/dev/null || echo 1; }

# ---- main loop ----------------------------------------------------------------
shopt -s nullglob
for src in "$BENCH_DIR"/*.rs; do
    bench="$(basename "$src" .rs)"
    echo "=== $bench ===" >&2

    # Per-variant output dirs (each compile emits one or more .o here; we link
    # them all). Re-created fresh per variant before each compile.
    d_llvm1="$SCRATCH/${bench}_llvm1"
    d_llvm3="$SCRATCH/${bench}_llvm3"
    d_brp="$SCRATCH/${bench}_brp"
    d_brn="$SCRATCH/${bench}_brn"

    b_llvm1="$SCRATCH/${bench}_llvm1.bin"
    b_llvm3="$SCRATCH/${bench}_llvm3.bin"
    b_br="$SCRATCH/${bench}_br.bin"

    # Each `time_wall` runs the compile $reps times (best-of) AND, via ERRFILE,
    # captures the last rep's stderr + sets LAST_RC — so the timed pass is also
    # the status/diagnostic source (no separate status compile, halving the
    # cost of the slow proof-gated bridge compiles).

    # --- LLVM O1 ---
    rm -rf "$d_llvm1"; mkdir -p "$d_llvm1"
    llvm_cmd "$src" "$d_llvm1" 1
    ERRFILE="$SCRATCH/err_llvm1"
    llvm1_c="$(time_wall "$COMPILE_REPS" "${CMD[@]}")"
    if [[ "$(rc_last)" -ne 0 ]]; then
        echo "  LLVM O1 compile FAILED (benchmark invalid?):" >&2
        sed 's/^/    /' "$SCRATCH/err_llvm1" >&2
        echo "$bench,NA,NA,NA,NA,NA,NA,NA,NA,NA,NA,LLVM_COMPILE_FAIL" >> "$OUT_CSV"
        continue
    fi

    # --- LLVM O3 ---
    rm -rf "$d_llvm3"; mkdir -p "$d_llvm3"
    llvm_cmd "$src" "$d_llvm3" 3
    ERRFILE=""
    llvm3_c="$(time_wall "$COMPILE_REPS" "${CMD[@]}")"

    # --- link + run LLVM binaries ---
    link_dir "$d_llvm1" "$b_llvm1"
    link_dir "$d_llvm3" "$b_llvm3"
    llvm1_e="$(time_cpu "$EXEC_REPS" "$b_llvm1")"; llvm_cs="$(rc_last)"
    llvm3_e="$(time_cpu "$EXEC_REPS" "$b_llvm3")"

    # --- BRIDGE (proofs ON, default) ---
    unset TCG_NO_PROOF_CERTS
    rm -rf "$d_brp"; mkdir -p "$d_brp"
    bridge_cmd "$src" "$d_brp"
    ERRFILE="$SCRATCH/err_brp"
    brp_c="$(time_wall "$BRIDGE_COMPILE_REPS" "${CMD[@]}")"
    if [[ "$(rc_last)" -ne 0 ]]; then
        echo "  BRIDGE (proofs on) FAILED CLOSED — coverage gap:" >&2
        head -8 "$SCRATCH/err_brp" | sed 's/^/    /' >&2
        echo "$bench,$llvm1_c,$llvm3_c,NA,NA,$llvm1_e,$llvm3_e,NA,$llvm_cs,NA,NA,BRIDGE_FAIL_CLOSED" >> "$OUT_CSV"
        continue
    fi

    # --- BRIDGE (proofs OFF) ---
    export TCG_NO_PROOF_CERTS=1
    rm -rf "$d_brn"; mkdir -p "$d_brn"
    bridge_cmd "$src" "$d_brn"
    ERRFILE=""
    brn_c="$(time_wall "$BRIDGE_COMPILE_REPS" "${CMD[@]}")"
    unset TCG_NO_PROOF_CERTS

    # --- link + run bridge binary (use proofs-on object; codegen is identical) ---
    if ! link_dir "$d_brp" "$b_br"; then
        echo "  BRIDGE link FAILED — coverage gap (unresolved symbols)" >&2
        echo "$bench,$llvm1_c,$llvm3_c,$brp_c,$brn_c,$llvm1_e,$llvm3_e,NA,$llvm_cs,NA,NA,BRIDGE_LINK_FAIL" >> "$OUT_CSV"
        continue
    fi
    br_e="$(time_cpu "$EXEC_REPS" "$b_br")"; br_cs="$(rc_last)"

    if [[ "$llvm_cs" == "$br_cs" ]]; then
        match="YES"
    else
        match="NO"
        echo "  !!! CHECKSUM MISMATCH: LLVM=$llvm_cs BRIDGE=$br_cs  (CORRECTNESS BUG) !!!" >&2
    fi

    echo "$bench,$llvm1_c,$llvm3_c,$brp_c,$brn_c,$llvm1_e,$llvm3_e,$br_e,$llvm_cs,$br_cs,$match,OK" >> "$OUT_CSV"
    echo "  ok  llvmO1_c=${llvm1_c}ms llvmO3_c=${llvm3_c}ms br_c=${brp_c}ms br_noproof_c=${brn_c}ms | llvmO1_e=${llvm1_e}ms llvmO3_e=${llvm3_e}ms br_e=${br_e}ms cs($llvm_cs vs $br_cs)=$match" >&2
done

echo "" >&2
echo "Wrote $OUT_CSV" >&2
