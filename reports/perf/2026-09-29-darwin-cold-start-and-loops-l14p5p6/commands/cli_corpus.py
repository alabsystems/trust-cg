#!/usr/bin/env python3
"""Byte-compare two trust-cg CLIs over every committed trust-ir text fixture
(`git ls-files '*.tir'`), generated scaling shapes (the scale_gate function
ladder, the pointer and stack-tuple blocks) for four targets at -O1 and -O3,
and the bridge-dumped `loops` modules (binary, aarch64-apple-darwin, -O1/-O2/
-O3). Objects both emit must be identical; refusals must be refusals on both
sides with the same message after normalizing timings and paths.

Usage: cli_corpus.py BASE_CLI HEAD_CLI WORKDIR
Environment: L14_CHECKOUT (repository checkout), L14_WORK (holds loops/loops<n>.tmbc
from dump_loops.py).
Measurement only; prints one line per case and a summary.
"""
import os, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

base, head, work = sys.argv[1:4]
W = os.environ["L14_CHECKOUT"]
S = os.environ["L14_WORK"]
GEN = f"{W}/reports/perf/2026-09-28-darwin-scaling-l14p6/commands"
os.makedirs(f"{work}/in", exist_ok=True)
os.makedirs(f"{work}/out", exist_ok=True)
cases = []
fixtures = subprocess.run(["git", "-C", W, "ls-files", "*.tir"], capture_output=True, text=True).stdout.split()
for rel in fixtures:
    flat = "fx_" + rel[:-4].replace("/", "_")
    dst = f"{work}/in/{flat}.tir"
    with open(f"{W}/{rel}", "rb") as src, open(dst, "wb") as out:
        out.write(src.read())
    cases.append((dst, "text"))
for n in (25, 100, 400):
    dst = f"{work}/in/scale_{n}.tir"
    subprocess.run([sys.executable, f"{GEN}/gen_tir.py", str(n), dst], check=True)
    cases.append((dst, "text"))
for m in (256, 1024):
    dst = f"{work}/in/ptr_{m}.tir"
    subprocess.run([sys.executable, f"{GEN}/gen_ptr.py", str(m), dst], check=True)
    cases.append((dst, "text"))
for m in (500, 513, 2000, 8000):
    dst = f"{work}/in/chain_{m}.tir"
    subprocess.run([sys.executable, f"{GEN}/gen_mem2.py", str(m), dst], check=True)
    cases.append((dst, "text"))
jobs = []
for path, fmt in cases:
    for target in ("aarch64-apple-darwin", "aarch64-unknown-linux-gnu",
                   "x86_64-unknown-linux-gnu", "x86_64-apple-darwin"):
        for opt in ("1", "3"):
            jobs.append((path, fmt, target, opt))
for n in (15, 30, 60, 120, 480):
    path = f"{S}/loops/loops{n}.tmbc"
    if os.path.exists(path):
        for opt in ("1", "2", "3"):
            jobs.append((path, "binary", "aarch64-apple-darwin", opt))


def normalize(text):
    text = re.sub(r"[0-9.]+ms", "", text)
    text = re.sub(r"/[^ ]*/target/release/build/([A-Za-z0-9_-]+)-[0-9a-f]{16}/", r"TARGET/build/\1/", text)
    return text.replace(work + "/", "")


def run(job):
    path, fmt, target, opt = job
    key = f"{os.path.basename(path)}.{target}.O{opt}"
    results = []
    for side, cli in (("base", base), ("head", head)):
        out = f"{work}/out/{key}.{side}.o"
        r = subprocess.run([cli, f"--format={fmt}", "-c", f"-O{opt}", "--target", target, "-o", out, path],
                           capture_output=True, text=True)
        data = open(out, "rb").read() if r.returncode == 0 and os.path.exists(out) else None
        if os.path.exists(out):
            os.unlink(out)
        results.append((r.returncode, data, normalize(r.stderr)))
    (rb, db, eb), (rh, dh, eh) = results
    if rb != rh:
        return f"RCMISMATCH {key} {rb} {rh}"
    if rb != 0:
        return f"FAILBOTH-{'SAMEERR' if eb == eh else 'DIFFERR'} {key} rc={rb}"
    return f"{'SAME' if db == dh else 'DIFF'} {key}"


with ThreadPoolExecutor(max_workers=3) as pool:
    lines = list(pool.map(run, jobs))
summary = {}
for line in lines:
    print(line)
    summary[line.split()[0]] = summary.get(line.split()[0], 0) + 1
print("SUMMARY", " ".join(f"{k}={v}" for k, v in sorted(summary.items())))
