#!/usr/bin/env python3
"""trustc -Z time-passes, LLVM vs bridge, min-of-N per pass, on one program.
Shows which rustc-level phases differ (the backend's compile_module is only
21-47ms of a 117-148ms compile; this attributes the REST).
usage: timepasses.py [--driver TRUSTC] N DYLIB PROG.rs   (driver: see _trust_driver.py)"""
import os, subprocess, sys, re, collections
from _trust_driver import resolve_from_argv
home = os.path.expanduser("~")
# STOCK EXCEPTION (Trust lacks rust-lld/gcc-ld; measured: no lib/rustlib/<host>/bin/{rust-lld,gcc-ld} in the Trust sysroot): the Linux linker shim comes from the stock stable toolchain's gcc-ld; the compilers come from the Trust package.
os.environ["PATH"] = f"{home}/.rustup/toolchains/stable-aarch64-unknown-linux-gnu/lib/rustlib/aarch64-unknown-linux-gnu/bin/gcc-ld:" + os.environ.get("PATH", "")
DRIVER = resolve_from_argv(sys.argv)
n = int(sys.argv[1]); dylib = sys.argv[2]; prog = sys.argv[3]
if n < 1:
    raise SystemExit("N must be at least 1")
rustc = DRIVER["compiler"]
flags = [*DRIVER["compiler_flags"], "--edition=2021", "--crate-type", "bin", "--target", "aarch64-unknown-linux-gnu", "-Cpanic=abort", "-Copt-level=3", "-Ztime-passes"]
pat = re.compile(r"time:\s+([0-9.]+);\s+rss:\s+\S+\s+->\s+\S+\s+\(\s*[+-]?\d+MB\)\s+(\S.*?)\s*$")
def run(backend):
    best = {}
    for _ in range(n):
        seen = {}
        cmd = [rustc] + ([f"-Zcodegen-backend={dylib}"] if backend else []) + flags + [prog, "-o", f"/tmp/tp_{os.getpid()}"]
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode != 0:
            sys.stderr.write(f"compile failed for {'bridge' if backend else 'LLVM'}:\n{r.stderr[-2000:]}\n")
            raise SystemExit(1)
        parsed = 0
        for line in r.stderr.splitlines():
            m = pat.search(line)
            if m:
                parsed += 1
                k = m.group(2).strip(); v = float(m.group(1)) * 1000
                seen[k] = seen.get(k, 0) + 1; k = f"{k}#{seen[k]}" if seen[k] > 1 else k
                best[k] = min(best.get(k, 1e9), v)
        if not parsed:
            raise SystemExit(f"no -Z time-passes rows parsed for {'bridge' if backend else 'LLVM'}")
    return best
L, B = run(False), run(True)
keys = sorted(set(L) | set(B), key=lambda k: -(B.get(k, 0) - L.get(k, 0)))
print(f"{'pass':45s} {'llvm ms':>8s} {'bridge ms':>9s} {'delta':>7s}")
for k in keys:
    l, b = L.get(k, 0.0), B.get(k, 0.0)
    if max(l, b) >= 0.3: print(f"{k[:45]:45s} {l:8.1f} {b:9.1f} {b-l:+7.1f}")
print(f"{'TOTAL (total pass)':45s} {L.get('total',0):8.1f} {B.get('total',0):9.1f}")
