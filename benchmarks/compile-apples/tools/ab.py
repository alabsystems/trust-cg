#!/usr/bin/env python3
"""Paired, interleaved compile-wall A/B: LLVM vs dylib A vs dylib B.

Mirrors benchmarks/beat-llvm/run.py's compile lane (same rustc, same flags,
time.monotonic wall, median of N) but interleaves L,A,B per iteration so drift
hits all three equally. Reports per-program medians, ratios, and the geomean.

usage: ab.py --a DYLIB [--b DYLIB] [--n 9] [--opt 2] PROG.rs ...
"""
import argparse, os, statistics, subprocess, sys, time, math, tempfile, shutil, resource

ap = argparse.ArgumentParser()
ap.add_argument("--a", required=True)
ap.add_argument("--b")
ap.add_argument("--n", type=int, default=9)
ap.add_argument("--opt", default="2")
ap.add_argument("--llvm-opt", default=None, help="opt level for the LLVM lane (default: same as --opt)")
ap.add_argument("--env", action="append", default=[], help="K=V passed to bridge lanes")
ap.add_argument("--benv", action="append", default=[], help="K=V passed to lane B only")
ap.add_argument("progs", nargs="+")
args = ap.parse_args()
if args.n < 1:
    ap.error("--n must be at least 1")

home = os.path.expanduser("~")
os.environ["PATH"] = f"{home}/.cargo/bin:{home}/.rustup/toolchains/stable-aarch64-unknown-linux-gnu/lib/rustlib/aarch64-unknown-linux-gnu/bin/gcc-ld:" + os.environ.get("PATH", "")
rustc = subprocess.check_output(["rustup", "which", "--toolchain", "nightly-2026-04-20", "rustc"], text=True).strip()
flags = ["--edition=2021", "--crate-type", "bin", "--target", "aarch64-unknown-linux-gnu", "-Cpanic=abort"]
llvm_opt = args.llvm_opt or args.opt
extra = dict(kv.split("=", 1) for kv in args.env)
bextra = dict(kv.split("=", 1) for kv in args.benv)

lanes = [("llvm", None), ("A", args.a)] + ([("B", args.b)] if args.b else [])
tmp = tempfile.mkdtemp(prefix="ab-", dir=os.environ.get("SCRATCH", None))
failures = 0

def one(prog, dylib, out, lane=None):
    cmd = [rustc] + ([f"-Zcodegen-backend={dylib}"] if dylib else []) + flags + [f"-Copt-level={args.opt if dylib else llvm_opt}", prog, "-o", out]
    env = dict(os.environ)
    if dylib:
        env.update(extra)
        if lane == "B":
            env.update(bextra)
    ru0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.monotonic()
    r = subprocess.run(cmd, env=env, capture_output=True, text=True)
    dt = time.monotonic() - t0
    ru1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    if r.returncode != 0:
        global failures
        failures += 1
        sys.stderr.write(f"FAIL {os.path.basename(prog)} lane={dylib or 'llvm'}\n{r.stderr[-2000:]}\n")
        return None
    return (dt, ru1.ru_utime - ru0.ru_utime, ru1.ru_stime - ru0.ru_stime)

results = {}  # prog -> lane -> [times]
for prog in args.progs:
    name = os.path.basename(prog).removesuffix(".rs")
    results[name] = {lane: [] for lane, _ in lanes}
    # warm-up once per lane (page cache, dylib load)
    for lane, dylib in lanes:
        one(prog, dylib, os.path.join(tmp, f"{name}.{lane}.warm"), lane)
    for i in range(args.n):
        for lane, dylib in lanes:
            dt = one(prog, dylib, os.path.join(tmp, f"{name}.{lane}.{i}"), lane)
            if dt is not None:
                results[name][lane].append(dt)
if failures:
    shutil.rmtree(tmp, ignore_errors=True)
    raise SystemExit(f"aborted: {failures} compile lane(s) failed")
def medk(xs, k): return statistics.median([x[k] for x in xs]) if xs else float("nan")

def geomean(xs):
    xs = [x for x in xs if x and not math.isnan(x)]
    return math.exp(sum(map(math.log, xs)) / len(xs)) if xs else float("nan")

hdr = f"{'prog':<16}{'llvm':>9}{'A':>9}" + (f"{'B':>9}" if args.b else "") + f"{'A/L':>8}" + (f"{'B/L':>8}{'B/A':>8}" if args.b else "") + "   user/sys ms: " + ("L | A | B" if args.b else "L | A")
print(hdr)
ra, rb = [], []
for name, lanes_t in results.items():
    l, a = medk(lanes_t["llvm"], 0) * 1000, medk(lanes_t["A"], 0) * 1000
    line = f"{name:<16}{l:>8.1f} {a:>8.1f} "
    ra.append(a / l)
    if args.b:
        b = medk(lanes_t["B"], 0) * 1000
        rb.append(b / l)
        line += f"{b:>8.1f} {a/l:>7.3f}x{b/l:>7.3f}x{b/a:>7.3f}x"
    else:
        line += f"{a/l:>7.3f}x"
    us = lambda ln: f"{medk(lanes_t[ln],1)*1000:.0f}/{medk(lanes_t[ln],2)*1000:.0f}"
    line += "   " + " | ".join(us(ln) for ln, _ in lanes)
    print(line)
print(f"{'geomean':<16}{'':>9}{'':>9}" + (f"{'':>9}" if args.b else "") + f"{geomean(ra):>7.3f}x" + (f"{geomean(rb):>7.3f}x" if args.b else ""))
shutil.rmtree(tmp, ignore_errors=True)
