#!/usr/bin/env python3
"""Compile compile-scaling's `loops` crates with a bridge dylib, dumping each
main CGU's trust-ir as <dir>/loops<n>.tmbc. The crates are compile-scaling's
generator output: `python3 benchmarks/compile-scaling/gen.py loops <n> > DIR/loops_<n>.rs`.
Usage: dump_loops.py DYLIB DIR [N,N,...]   Environment: TRUST_PKG."""
import glob, os, shutil, subprocess, sys

PKG = os.environ["TRUST_PKG"]
dylib, d = sys.argv[1], sys.argv[2]
cache = os.path.join(d, "cache")
os.makedirs(cache, mode=0o700, exist_ok=True)
for n in [int(x) for x in (sys.argv[3].split(",") if len(sys.argv) > 3 else ["15", "30", "60", "120"])]:
    dump = os.path.join(d, f"dump{n}")
    shutil.rmtree(dump, ignore_errors=True)
    os.makedirs(dump)
    cmd = [f"{PKG}/bin/trustc", "-Ztrust-verify=off", f"-Zcodegen-backend={dylib}",
           "-Ztrust-ir-cg-args=no-proof-certs", "-Ztrust-ir-cg-args=refine-solver=0",
           f"-Ztrust-ir-cg-args=dump-trust-ir={dump}",
           "--edition=2021", "--crate-type", "bin", "-Cpanic=abort", "-Coverflow-checks=off",
           "-Ccodegen-units=1", "-Cdefault-linker-libraries=y", "-Copt-level=2",
           "-o", os.path.join(d, f"loops_{n}"), os.path.join(d, f"loops_{n}.rs")]
    env = {k: v for k, v in os.environ.items() if not k.startswith(("TCG_", "TRUST_CG_"))}
    env["XDG_CACHE_HOME"] = cache
    r = subprocess.run(cmd, env=env, capture_output=True, text=True)
    main = [p for p in glob.glob(os.path.join(dump, "*-cgu.0.rcgu.trust_irbin"))]
    print(n, r.returncode, main)
    if main:
        shutil.copy(main[0], os.path.join(d, f"loops{n}.tmbc"))
