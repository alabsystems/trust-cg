#!/usr/bin/env python3
"""Compile-time SCALING gate: catch superlinear blowups the corpus cannot see.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0

For each shape, compile at doubling sizes with LLVM and with trust-cg and report
the growth EXPONENT of each. LLVM is the control: if both grow at the same rate
the backend simply costs a constant factor more, which is a different (and much
less serious) problem than growing faster.

    exponent k from t ~ n^k, fitted across the size ladder.
    k ~ 1.0  linear        healthy
    k ~ 2.0  quadratic     a whole-function scan inside a per-item loop
    k ~ 3.0  cubic         dense-set dataflow, e.g. dominator sets

Exits non-zero when trust-cg's exponent exceeds LLVM's by more than
--max-excess (default 0.6), or when a compile fails.
"""
import argparse, math, os, pathlib, resource, statistics, subprocess, sys, time

REPO = pathlib.Path(__file__).resolve().parents[2]
GEN = pathlib.Path(__file__).resolve().parent / "gen.py"
DYLIB_REL = "crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so"
PROOFS_OFF = {"TCG_NO_PROOF_CERTS": "1", "TCG_REFINE_SOLVER": "0"}
BASE = ["--edition=2021", "--crate-type", "bin", "-Cpanic=abort", "-Coverflow-checks=off",
        "-Ccodegen-units=1", "-Cdefault-linker-libraries=y"]


def rustc_path() -> str:
    out = subprocess.run(["rustup", "which", "--toolchain", "nightly-2026-04-20", "rustc"],
                         capture_output=True, text=True)
    return out.stdout.strip() if out.returncode == 0 else "rustc"


def cpu_ms(cmd, extra=None):
    env = dict(os.environ)
    env.update(PROOFS_OFF)
    env.update(extra or {})
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    r = subprocess.run(cmd, capture_output=True, env=env)
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    used = (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime)
    return used * 1000.0, r.returncode == 0


def exponent(sizes, times):
    """Least-squares slope of log(t) against log(n) — the growth exponent."""
    xs = [math.log(n) for n in sizes]
    ys = [math.log(max(t, 1e-6)) for t in times]
    mx, my = statistics.mean(xs), statistics.mean(ys)
    num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    den = sum((x - mx) ** 2 for x in xs)
    return num / den if den else 0.0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--shapes", nargs="*", default=["blocks", "loops", "funcs", "arraysize"])
    ap.add_argument("--sizes", nargs="*", type=int, default=None)
    ap.add_argument("-n", type=int, default=3, help="median-of-N per point")
    ap.add_argument("--dylib", default=None)
    ap.add_argument("--out-dir", default=None)
    ap.add_argument("--max-excess", type=float, default=0.6,
                    help="fail if tcg's exponent exceeds LLVM's by more than this")
    args = ap.parse_args()

    dylib = pathlib.Path(args.dylib) if args.dylib else REPO / DYLIB_REL
    if not dylib.exists():
        print(f"compile-scaling: FATAL: bridge dylib missing: {dylib}")
        return 2
    rustc = rustc_path()
    work = pathlib.Path(args.out_dir) if args.out_dir else REPO / "benchmarks" / "compile-scaling" / "results"
    work.mkdir(parents=True, exist_ok=True)

    # Loop shapes are far heavier per unit, so they get a smaller ladder.
    default_sizes = {"blocks": [100, 200, 400, 800], "loops": [15, 30, 60, 120],
                     "funcs": [50, 100, 200, 400],
                     "arraysize": [4096, 16384, 65536, 262144]}
    failures = []
    for shape in args.shapes:
        sizes = args.sizes or default_sizes[shape]
        lt, tt = [], []
        print(f"\n=== shape={shape}")
        print(f"  {'n':>6}{'LLVM':>11}{'trust-cg':>12}{'ratio':>8}")
        for n in sizes:
            src = work / f"{shape}_{n}.rs"
            src.write_text(subprocess.run([sys.executable, str(GEN), shape, str(n)],
                                          capture_output=True, text=True).stdout)
            lms = [cpu_ms([rustc, *BASE, "-Copt-level=2", "-o", str(work / "l"), str(src)]) for _ in range(args.n)]
            tms = [cpu_ms([rustc, f"-Zcodegen-backend={dylib}", *BASE, "-Copt-level=2",
                           "-o", str(work / "t"), str(src)]) for _ in range(args.n)]
            if not all(ok for _, ok in lms + tms):
                print(f"  {n:>6}   COMPILE FAILED")
                failures.append(f"{shape}/{n}: compile failed")
                continue
            l = statistics.median(v for v, _ in lms)
            t = statistics.median(v for v, _ in tms)
            lt.append(l); tt.append(t)
            print(f"  {n:>6}{l:>10.1f}ms{t:>11.1f}ms{t / l:>8.2f}x")
        if len(lt) >= 3:
            kl, kt = exponent(sizes[:len(lt)], lt), exponent(sizes[:len(tt)], tt)
            verdict = "OK" if kt - kl <= args.max_excess else "*** SUPERLINEAR vs LLVM ***"
            print(f"  growth exponent: LLVM {kl:.2f}   trust-cg {kt:.2f}   excess {kt - kl:+.2f}   {verdict}")
            if kt - kl > args.max_excess:
                failures.append(f"{shape}: exponent {kt:.2f} vs LLVM {kl:.2f} (excess {kt - kl:+.2f})")

    print()
    if failures:
        print("compile-scaling: FAIL")
        for f in failures:
            print(f"  {f}")
        return 1
    print("compile-scaling: OK — no shape grows materially faster than LLVM")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
