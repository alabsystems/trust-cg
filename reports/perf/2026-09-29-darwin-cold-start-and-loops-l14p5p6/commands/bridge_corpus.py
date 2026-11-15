#!/usr/bin/env python3
"""Byte-compare two bridge backends over the repository's Rust benchmark
programs (beat-llvm, shape-coverage and decline-shapes `progs/*.rs`), proofs
off, aarch64-apple-darwin, with -C save-temps: every object rustc keeps plus
the linked binary (same output name in per-backend directories, since ld64's
ad-hoc signature names the output file). Measurement only.

Usage: bridge_corpus.py BASE_DYLIB HEAD_DYLIB OPT WORKDIR CHECKOUT
Environment: TRUST_PKG (Trust package root).
"""
import filecmp, glob, os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

PKG = os.environ["TRUST_PKG"]
base, head, opt, work, checkout = sys.argv[1:6]
env = {k: v for k, v in os.environ.items() if not k.startswith(("TCG_", "TRUST_CG_"))}
env["XDG_CACHE_HOME"] = os.path.join(work, "cache")
os.makedirs(env["XDG_CACHE_HOME"], mode=0o700, exist_ok=True)
sources = []
for group in ("beat-llvm", "shape-coverage", "decline-shapes"):
    sources += sorted(glob.glob(f"{checkout}/benchmarks/{group}/progs/*.rs"))


def compile_both(src):
    name = os.path.splitext(os.path.basename(src))[0]
    group = os.path.basename(os.path.dirname(os.path.dirname(src)))
    rcs, dirs = [], []
    for tag, dylib in (("base", base), ("head", head)):
        d = os.path.join(work, f"O{opt}", tag, group, name)
        os.makedirs(d, exist_ok=True)
        r = subprocess.run([f"{PKG}/bin/trustc", "-Ztrust-verify=off", f"-Zcodegen-backend={dylib}",
                            "-Ztrust-ir-cg-args=no-proof-certs", "--edition=2021", "--crate-type", "bin",
                            "--target", "aarch64-apple-darwin", "-Cpanic=abort", f"-Copt-level={opt}",
                            "-C", "save-temps", "-o", os.path.join(d, "prog"), src],
                           cwd=d, env=env, capture_output=True, text=True)
        rcs.append(r.returncode)
        dirs.append(d)
    if rcs[0] != rcs[1]:
        return [f"RCMISMATCH {group}/{name} {rcs}"]
    if rcs[0] != 0:
        return [f"FAILBOTH {group}/{name} rc={rcs[0]}"]
    lines = []
    files = sorted(f for f in os.listdir(dirs[0]) if f == "prog" or f.endswith(".o"))
    for f in files:
        other = os.path.join(dirs[1], f)
        same = os.path.exists(other) and filecmp.cmp(os.path.join(dirs[0], f), other, shallow=False)
        lines.append(f"{'SAME' if same else 'DIFF'} {group}/{name}/{f}")
    return lines


with ThreadPoolExecutor(max_workers=3) as pool:
    results = [line for lines in pool.map(compile_both, sources) for line in lines]
counts = {}
for line in results:
    print(line)
    counts[line.split()[0]] = counts.get(line.split()[0], 0) + 1
print(f"O{opt} programs={len(sources)}", " ".join(f"{k}={v}" for k, v in sorted(counts.items())))
