#!/usr/bin/env python3
"""Per-pass corpus time for two dylibs (TRUST_CG_TIME_PASSES): per program the
min-of-N of each pass's per-compile SUM (all functions, all iterations), then
summed over the corpus.
usage: pass_times.py [--driver TRUSTC] N DYLIB_A DYLIB_B [pass ...]   (driver: see _trust_driver.py)"""
import os, subprocess, sys, glob, re, collections
from _trust_driver import resolve_from_argv
home = os.path.expanduser("~")
# STOCK EXCEPTION (Trust lacks rust-lld/gcc-ld; measured: no lib/rustlib/<host>/bin/{rust-lld,gcc-ld} in the Trust sysroot): the Linux linker shim comes from the stock stable toolchain's gcc-ld; the compilers come from the Trust package.
os.environ["PATH"] = f"{home}/.rustup/toolchains/stable-aarch64-unknown-linux-gnu/lib/rustlib/aarch64-unknown-linux-gnu/bin/gcc-ld:" + os.environ.get("PATH", "")
DRIVER = resolve_from_argv(sys.argv)
n = int(sys.argv[1]); A, B = sys.argv[2], sys.argv[3]; only = set(sys.argv[4:])
if n < 1:
    raise SystemExit("N must be at least 1")
rustc = DRIVER["compiler"]
flags = [*DRIVER["compiler_flags"], "--edition=2021", "--crate-type", "bin", "--target", "aarch64-unknown-linux-gnu", "-Cpanic=abort", "-Copt-level=3"]
pat = re.compile(r"\[trust-cg-time-pass\] end func=\S+ iter=\d+ pass=(\S+) changed=\S+ elapsed_us=(\d+)")
env = dict(os.environ, TRUST_CG_TIME_PASSES="1")
tot = {"A": collections.Counter(), "B": collections.Counter()}
progs = sorted(glob.glob(os.environ.get("TCG_PROGS", os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../beat-llvm/progs")) + "/*.rs"))
if not progs:
    raise SystemExit("no corpus programs found")
for p in progs:
    for label, d in (("A", A), ("B", B)):
        best = collections.defaultdict(lambda: 1e18)
        for _ in range(n):
            r = subprocess.run([rustc, f"-Zcodegen-backend={d}"] + flags + [p, "-o", f"/tmp/pt_{os.getpid()}"], env=env, capture_output=True, text=True)
            if r.returncode != 0:
                sys.stderr.write(f"compile failed for {p} lane {label}:\n{r.stderr[-2000:]}\n")
                raise SystemExit(1)
            st = collections.Counter()
            for m in pat.finditer(r.stderr):
                if "bookkeeping" in m.group(1): continue
                st[m.group(1)] += int(m.group(2))
            if not st:
                raise SystemExit(f"no pass-timing rows parsed for {p} lane {label}")
            for k, v in st.items(): best[k] = min(best[k], v)
        for k, v in best.items(): tot[label][k] += v
keys = [k for k in tot["A"] if not only or k in only]
keys.sort(key=lambda k: -tot["A"][k])
print(f"{'pass':32s} {'A ms':>8s} {'B ms':>8s} {'B/A':>6s}")
for k in keys[:40]:
    a, b = tot["A"][k] / 1000, tot["B"][k] / 1000
    print(f"{k:32s} {a:8.2f} {b:8.2f} {(b / a if a else 0):6.3f}")
ta, tb = sum(tot["A"].values()) / 1000, sum(tot["B"].values()) / 1000
if ta == 0:
    raise SystemExit("lane A produced zero pass time")
print(f"{'TOTAL pass time':32s} {ta:8.2f} {tb:8.2f} {tb / ta:6.3f}")
