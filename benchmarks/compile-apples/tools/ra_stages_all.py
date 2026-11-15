#!/usr/bin/env python3
"""All regalloc stage timers in one pass: per program, min-of-N of each
stage's per-compile SUM across functions; then summed over the corpus.
usage: ra_stages_all.py [--driver TRUSTC] N DYLIB [DYLIB_B]   (driver: see _trust_driver.py)"""
import os, subprocess, sys, glob, re, collections
from _trust_driver import resolve_from_argv
home = os.path.expanduser("~")
# STOCK EXCEPTION (Trust lacks rust-lld/gcc-ld; measured: no lib/rustlib/<host>/bin/{rust-lld,gcc-ld} in the Trust sysroot): the Linux linker shim comes from the stock stable toolchain's gcc-ld; the compilers come from the Trust package.
os.environ["PATH"] = f"{home}/.rustup/toolchains/stable-aarch64-unknown-linux-gnu/lib/rustlib/aarch64-unknown-linux-gnu/bin/gcc-ld:" + os.environ.get("PATH", "")
DRIVER = resolve_from_argv(sys.argv)
n = int(sys.argv[1]); dylibs = sys.argv[2:]
if n < 1:
    raise SystemExit("N must be at least 1")
if not dylibs:
    raise SystemExit("at least one DYLIB is required")
rustc = DRIVER["compiler"]
flags = [*DRIVER["compiler_flags"], "--edition=2021", "--crate-type", "bin", "--target", "aarch64-unknown-linux-gnu", "-Cpanic=abort", "-Copt-level=3"]
pat = re.compile(r"\[trust-cg-time-regalloc\] func=(\S+) pass=\S+ stage=(\S+) elapsed_us=(\d+)")
env = dict(os.environ, TRUST_CG_TIME_PASSES="1")
progs = sorted(glob.glob(os.environ.get("TCG_PROGS", os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../beat-llvm/progs")) + "/*.rs"))
if not progs:
    raise SystemExit("no corpus programs found")
tot = [collections.Counter() for _ in dylibs]; cnt = [collections.Counter() for _ in dylibs]
for p in progs:
    for lane, d in enumerate(dylibs):
        best = {}
        for _ in range(n):
            r = subprocess.run([rustc, f"-Zcodegen-backend={d}"] + flags + [p, "-o", f"/tmp/ra_all_{os.getpid()}"], env=env, capture_output=True, text=True)
            if r.returncode != 0:
                sys.stderr.write(f"compile failed for {p} lane {lane + 1}:\n{r.stderr[-2000:]}\n")
                raise SystemExit(1)
            st = collections.Counter(); sc = collections.Counter()
            for m in pat.finditer(r.stderr): st[m.group(2)] += int(m.group(3)); sc[m.group(2)] += 1
            if not st:
                raise SystemExit(f"no regalloc timing rows parsed for {p} lane {lane + 1}")
            for k, v in st.items():
                if k not in best or v < best[k][0]:
                    best[k] = (v, sc[k])
        for k, (value, count) in best.items():
            tot[lane][k] += value
            cnt[lane][k] += count
stages = sorted(set(k for lane in tot for k in lane), key=lambda k: -tot[0][k])
print(f"{'stage (corpus sum, ms)':28s}" + "".join(f"{os.path.basename(d)[:18]:>20s}" for d in dylibs) + ("      B/A" if len(dylibs) > 1 else ""))
for k in stages:
    a = tot[0][k] / 1000
    row = f"{k:28s}{a:20.2f} (n={cnt[0][k]})"
    if len(dylibs) > 1:
        b = tot[1][k] / 1000; row += f"{b:20.2f} (n={cnt[1][k]}){(b / a if a else 0):9.3f}"
    print(row)
