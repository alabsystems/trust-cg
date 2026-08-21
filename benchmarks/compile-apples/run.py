#!/usr/bin/env python3
"""Apples-to-apples COMPILE-TIME comparison: trust-cg proofs-off vs LLVM.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0

WHY THIS EXISTS
---------------
`benchmarks/beat-llvm` measures the PRODUCTION lane (certs + solver + cache on)
and deliberately refuses to mark a proof-weakened run `headline_eligible`. That
is the right policy for a headline number, but it leaves the lane we actually
optimise against untracked.

The target this measures is narrow and specific: with verification turned OFF
on both sides -- rustc's LLVM backend at `-C opt-level=N` versus trust-cg at the
same `-C opt-level=N` -- trust-cg should be strictly faster to compile on EVERY
program, not merely at parity in the geomean. Once that holds, verification cost
gets added back on top of a lane that is already ahead.

MEASUREMENT DISCIPLINE
----------------------
* **Interleaved A/B.** Each repetition compiles LLVM then trust-cg back to back,
  so machine drift (thermal, other load) hits both arms equally. Measuring all
  LLVM reps then all trust-cg reps attributes drift to the backend.
* **Real output files.** Never `-o /dev/null`: it changes what the linker does
  and is not the thing users pay for.
* **Median, not mean.** One descheduled run should not move the number.
* **Load gate.** A loaded machine produces numbers that are not evidence.
"""
import argparse
import json
import math
import os
import pathlib
import resource
import statistics
import subprocess
import sys
import time

REPO = pathlib.Path(__file__).resolve().parents[2]
PROGS = REPO / "benchmarks" / "beat-llvm" / "progs"
DYLIB_REL = "crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so"
PROOFS_OFF = {"TCG_NO_PROOF_CERTS": "1", "TCG_REFINE_SOLVER": "0"}
BASE = [
    "--edition=2021", "--crate-type", "bin", "-Cpanic=abort",
    "-Coverflow-checks=off", "-Ccodegen-units=1", "-Cdefault-linker-libraries=y",
]


def rustc_path() -> str:
    out = subprocess.run(
        ["rustup", "which", "--toolchain", "nightly-2026-04-20", "rustc"],
        capture_output=True, text=True,
    )
    return out.stdout.strip() if out.returncode == 0 else "rustc"


def compile_once(rustc, src, out, opt, dylib=None):
    """Compile once; return (cpu_seconds, wall_seconds), or None if it failed.

    CPU time is the PRIMARY signal. These compiles are ~120ms wall and the
    difference we are chasing is 5-15ms, which is the same size as the
    scheduling noise on a shared box -- two back-to-back wall-clock runs of the
    identical binary moved a program from 1.153x to 0.994x. Child CPU time
    (user+sys) is not perturbed by descheduling, so it separates "our compiler
    did more work" from "the machine was busy".
    """
    cmd = [rustc, *BASE, f"-Copt-level={opt}", "-o", str(out), str(src)]
    env = dict(os.environ)
    if dylib:
        cmd.insert(1, f"-Zcodegen-backend={dylib}")
        env.update(PROOFS_OFF)
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.perf_counter()
    r = subprocess.run(cmd, capture_output=True, env=env)
    wall = time.perf_counter() - t0
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime)
    return (cpu, wall) if r.returncode == 0 else None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--opt", default="2", help="-C opt-level for BOTH arms")
    ap.add_argument("-n", type=int, default=5, help="repetitions (median-of-N)")
    ap.add_argument("--dylib", default=None)
    ap.add_argument("--progs", nargs="*", default=None)
    ap.add_argument("--out-dir", default=None)
    ap.add_argument("--allow-loaded", action="store_true")
    ap.add_argument("--load-threshold", type=float, default=2.0)
    args = ap.parse_args()

    load1 = os.getloadavg()[0]
    if load1 > args.load_threshold and not args.allow_loaded:
        print(f"compile-apples: FATAL: 1-min load {load1:.2f} > {args.load_threshold}; "
              f"a loaded machine does not produce evidence (use --allow-loaded to override)")
        return 2

    dylib = pathlib.Path(args.dylib) if args.dylib else REPO / DYLIB_REL
    if not dylib.exists():
        print(f"compile-apples: FATAL: bridge dylib missing: {dylib}")
        return 2
    # Refuse to attribute results to a tree the dylib was not built from.
    newest_src = max(
        (p.stat().st_mtime for p in (REPO / "crates").rglob("*.rs")), default=0
    )
    if newest_src > dylib.stat().st_mtime:
        print(f"compile-apples: FATAL: bridge dylib is STALE (a .rs file is newer). "
              f"Rebuild before measuring.")
        return 2

    rustc = rustc_path()
    out_dir = pathlib.Path(args.out_dir) if args.out_dir else REPO / "benchmarks" / "compile-apples" / "results"
    work = out_dir / "work"
    work.mkdir(parents=True, exist_ok=True)

    stems = args.progs or sorted(p.stem for p in PROGS.glob("*.rs"))
    rows, ratios, losers = [], [], []

    for stem in stems:
        src = PROGS / f"{stem}.rs"
        if not src.exists():
            continue
        # Warm up both arms; discard. First compile pays page-in costs.
        compile_once(rustc, src, work / f"w_l_{stem}", args.opt)
        compile_once(rustc, src, work / f"w_t_{stem}", args.opt, dylib)

        lt, tt = [], []
        declined = False
        for _ in range(args.n):
            # INTERLEAVED: llvm then tcg, same repetition.
            a = compile_once(rustc, src, work / f"l_{stem}", args.opt)
            b = compile_once(rustc, src, work / f"t_{stem}", args.opt, dylib)
            if a is None:
                print(f"  {stem}: LLVM ORACLE FAILED — skipping")
                declined = True
                break
            if b is None:
                declined = True
                break
            lt.append(a)
            tt.append(b)
        if declined and not tt:
            rows.append({"prog": stem, "verdict": "DECLINED"})
            print(f"  {stem:<18} DECLINED (trust-cg failed closed)")
            continue

        lm = statistics.median(c for c, _ in lt)
        tm = statistics.median(c for c, _ in tt)
        lw = statistics.median(w for _, w in lt)
        tw = statistics.median(w for _, w in tt)
        ratio = tm / lm            # CPU ratio: the primary signal
        wratio = tw / lw
        ratios.append(ratio)
        if ratio >= 1.0:
            losers.append((stem, ratio))
        rows.append({"prog": stem, "llvm_cpu_s": round(lm, 4), "tcg_cpu_s": round(tm, 4),
                     "cpu_ratio": round(ratio, 4),
                     "llvm_wall_s": round(lw, 4), "tcg_wall_s": round(tw, 4),
                     "wall_ratio": round(wratio, 4)})
        flag = "  SLOWER" if ratio >= 1.0 else ""
        print(f"  {stem:<18} cpu llvm {lm:.4f}s  tcg {tm:.4f}s  {ratio:.3f}x"
              f"   (wall {wratio:.3f}x){flag}")

    if not ratios:
        print("compile-apples: no measurable rows")
        return 1

    geo = math.exp(sum(math.log(r) for r in ratios) / len(ratios))
    print()
    print(f"compile-apples: -C opt-level={args.opt}, median-of-{args.n}, interleaved A/B")
    print(f"  geomean CPU compile ratio (tcg proofs-off / llvm): {geo:.4f}x")
    print(f"  strictly faster on {sum(1 for r in ratios if r < 1.0)}/{len(ratios)} programs")
    if losers:
        worst = ", ".join(f"{s} {r:.3f}" for s, r in sorted(losers, key=lambda x: -x[1]))
        print(f"  NOT YET FASTER on {len(losers)}: {worst}")
    else:
        print("  TARGET MET: strictly faster on every measured program.")

    out_dir.mkdir(parents=True, exist_ok=True)
    stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    payload = {"opt": args.opt, "n": args.n, "geomean": geo, "load1": load1, "rows": rows}
    (out_dir / f"compile-apples-{stamp}.json").write_text(json.dumps(payload, indent=2))
    print(f"\nresults: {out_dir}/compile-apples-{stamp}.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
