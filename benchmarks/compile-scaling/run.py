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

Driver: the bridge pins channel = "trust", so both arms use the Trust compiler
that pin names. scripts/trust_toolchain.py resolves the PATH trustc/targo package,
or the package trustc named by --driver, and refuses the retired stock
nightly-2026-04-20 and any unidentified compiler (exit 2). Both arms compile in
Trust's explicit unverified frontend lane (-Ztrust-verify=off), the vanilla
frontend this gate always measured; that lane is diagnostic and makes no
Trust-verified compilation claim.

Backend: the newest built librustc_codegen_trust_cg with this host's
shared-library suffix (scripts/bridge_backend.py, the rule run.py and
scale_gate.py share), or --dylib; a backend older than its build inputs is
refused unless --allow-stale-dylib is given. The default used to be a fixed
Linux `.so` path, so on Darwin the gate could not find a backend at all. Both
arms compile for the Trust compiler's host (no --target is passed).
"""
import argparse, importlib.util, math, os, pathlib, resource, statistics, subprocess, sys, time

REPO = pathlib.Path(__file__).resolve().parents[2]
GEN = pathlib.Path(__file__).resolve().parent / "gen.py"
# Proof certificates and the refinement solver are switched off through the
# backend's TRACKED knob option; trustc refuses the former TCG_NO_PROOF_CERTS /
# TCG_REFINE_SOLVER environment variables as untracked codegen controls.
PROOFS_OFF_FLAGS = ["-Ztrust-ir-cg-args=no-proof-certs", "-Ztrust-ir-cg-args=refine-solver=0"]
BASE = ["--edition=2021", "--crate-type", "bin", "-Cpanic=abort", "-Coverflow-checks=off",
        "-Ccodegen-units=1", "-Cdefault-linker-libraries=y"]


_TRUST_SPEC = importlib.util.spec_from_file_location(
    "trust_cg_trust_toolchain", REPO / "scripts" / "trust_toolchain.py")
TRUST_TOOLCHAIN = importlib.util.module_from_spec(_TRUST_SPEC)
_TRUST_SPEC.loader.exec_module(TRUST_TOOLCHAIN)
_BACKEND_SPEC = importlib.util.spec_from_file_location(
    "trust_cg_bridge_backend", REPO / "scripts" / "bridge_backend.py")
BRIDGE_BACKEND = importlib.util.module_from_spec(_BACKEND_SPEC)
_BACKEND_SPEC.loader.exec_module(BRIDGE_BACKEND)
# Explicit unverified frontend lane for both arms (see Driver above).
LANE_FLAGS = list(TRUST_TOOLCHAIN.UNVERIFIED_COMPILER_FLAGS)


def resolve_driver(explicit=None):
    """The pinned Trust compiler record, or None after reporting why it is unusable."""
    try:
        return TRUST_TOOLCHAIN.resolve(explicit)
    except TRUST_TOOLCHAIN.ToolchainError as error:
        print(f"compile-scaling: FATAL: cannot resolve the pinned Trust compiler: {error}")
        return None


def default_dylib(repo=REPO):
    """The backend used without --dylib: the newest built one with this host's
    suffix, else the canonical build location (reported missing by main)."""
    return BRIDGE_BACKEND.newest(repo) or BRIDGE_BACKEND.candidates(repo)[0]


def cpu_ms(cmd, extra=None):
    env = dict(os.environ)
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
    ap.add_argument("--dylib", default=None,
                    help="bridge backend (default: the newest built one for this host)")
    ap.add_argument("--allow-stale-dylib", action="store_true",
                    help="measure a backend older than its build inputs (NOT evidence)")
    ap.add_argument("--driver", default=None,
                    help="explicit Trust package trustc (default: the PATH trustc/targo package)")
    ap.add_argument("--out-dir", default=None)
    ap.add_argument("--max-excess", type=float, default=0.6,
                    help="fail if tcg's exponent exceeds LLVM's by more than this")
    args = ap.parse_args()

    dylib = pathlib.Path(args.dylib) if args.dylib else default_dylib()
    if not dylib.exists():
        print(f"compile-scaling: FATAL: bridge dylib missing: {dylib}")
        return 2
    stale = BRIDGE_BACKEND.stale_source(REPO, dylib)
    if stale is not None and not args.allow_stale_dylib:
        print(f"compile-scaling: FATAL: bridge dylib is STALE ({stale} is newer); rebuild it, "
              "or pass --allow-stale-dylib (such a run is NOT evidence)")
        return 2
    driver = resolve_driver(args.driver)
    if driver is None:
        return 2
    rustc = driver["compiler"]
    print(f"compile-scaling: driver {TRUST_TOOLCHAIN.summary(driver)}")
    print(f"compile-scaling: target {driver['host']} (driver host); backend {dylib}"
          f"{' (STALE override: not evidence)' if stale is not None else ''}")
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
            lms = [cpu_ms([rustc, *LANE_FLAGS, *BASE, "-Copt-level=2", "-o", str(work / "l"), str(src)]) for _ in range(args.n)]
            tms = [cpu_ms([rustc, *LANE_FLAGS, f"-Zcodegen-backend={dylib}", *PROOFS_OFF_FLAGS, *BASE, "-Copt-level=2",
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
