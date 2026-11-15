#!/usr/bin/env python3
"""Fixpoint-convergence scan (the check that found the vectorizer remainder
re-fire class, 2026-08-27): compile every corpus program with
TRUST_CG_TIME_PASSES=1 and report, per function, (a) any pass that still
reports changed=true in the LAST fixpoint iteration and (b) instruction
counts that GROW between iterations. Both are non-idempotent-pass suspects.
usage: fixpoint_scan.py [--driver TRUSTC] DYLIB   (TCG_PROGS overrides the corpus dir;
driver: see _trust_driver.py)"""
import os, subprocess, sys, glob, re, collections
from _trust_driver import resolve_from_argv
home = os.path.expanduser("~")
# STOCK EXCEPTION (Trust lacks rust-lld/gcc-ld; measured: no lib/rustlib/<host>/bin/{rust-lld,gcc-ld} in the Trust sysroot): the Linux linker shim comes from the stock stable toolchain's gcc-ld; the compilers come from the Trust package.
os.environ["PATH"] = f"{home}/.rustup/toolchains/stable-aarch64-unknown-linux-gnu/lib/rustlib/aarch64-unknown-linux-gnu/bin/gcc-ld:" + os.environ.get("PATH", "")
DRIVER = resolve_from_argv(sys.argv)
dylib = sys.argv[1]
rustc = DRIVER["compiler"]
flags = [*DRIVER["compiler_flags"], "--edition=2021", "--crate-type", "bin", "--target", "aarch64-unknown-linux-gnu", "-Cpanic=abort", "-Copt-level=3"]
pat = re.compile(r"\[trust-cg-time-pass\] end func=(\S+) iter=(\d+) pass=(\S+) changed=(true|false) elapsed_us=(\d+) blocks=(\d+) insts=(\d+)")
progs = sorted(glob.glob(os.environ.get("TCG_PROGS", os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../beat-llvm/progs")) + "/*.rs"))
if not progs:
    raise SystemExit("no corpus programs found")
suspects = 0
for p in progs:
    r = subprocess.run([rustc, f"-Zcodegen-backend={dylib}"] + flags + [p, "-o", f"/tmp/fxs_{os.getpid()}"], env=dict(os.environ, TRUST_CG_TIME_PASSES="1"), capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write(f"compile failed for {p}:\n{r.stderr[-2000:]}\n")
        raise SystemExit(1)
    per = collections.defaultdict(list)
    for m in pat.finditer(r.stderr):
        per[m.group(1)].append((int(m.group(2)), m.group(3), m.group(4) == "true", int(m.group(7))))
    if not per:
        raise SystemExit(f"no pass-timing rows parsed for {p}")
    for fn, rows in per.items():
        iters = sorted({x[0] for x in rows}); last = iters[-1]
        ends = [[x for x in rows if x[0] == it][-1][3] for it in iters]
        changers = [x[1] for x in rows if x[0] == last and x[2]]
        grew = any(b > a for a, b in zip(ends, ends[1:]))
        if changers or grew:
            suspects += 1
            print(f"{os.path.basename(p)[:-3]:16s} {fn[-40:]:40s} iters={len(iters)} insts={ends} last-iteration changers={changers}{'  GROWING' if grew else ''}")
print(f"{suspects} suspect function(s) over {len(progs)} programs")
