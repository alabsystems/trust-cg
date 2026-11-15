#!/usr/bin/env python3
"""Warm-compile attribution of the beat-llvm corpus: LLVM -O2 against one or more
bridge dylibs (-O3, no-proof-certs, warm private cache), interleaved, N samples.
Records instructions retired, max RSS, wall (with 1-minute load) from
/usr/bin/time -l, and, in an extra traced run per backend, the bridge's own
`time` phase lines. Testing evidence only."""
import argparse, json, os, re, statistics, subprocess, tempfile
from pathlib import Path

def load1():
    t = subprocess.run(["sysctl", "-n", "vm.loadavg"], capture_output=True, text=True).stdout
    return float(re.findall(r"[\d.]+", t)[0])

def parse_time(err):
    d = {}
    m = re.search(r"^\s*([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys", err, re.M)
    if m:
        d["wall"], d["user"], d["sys"] = map(float, m.groups())
    for k, p in (("instr", r"(\d+)\s+instructions retired"), ("rss", r"(\d+)\s+maximum resident set size"),
                 ("footprint", r"(\d+)\s+peak memory footprint")):
        m = re.search(p, err)
        d[k] = int(m.group(1)) if m else None
    return d

def run(args, src, backend, opt, cache, out, extra=()):
    cmd = ["/usr/bin/time", "-l", args.driver, "-Ztrust-verify=off", "--edition=2021", "--crate-type", "bin",
           "--target", "aarch64-apple-darwin", "-Cpanic=abort", f"-Copt-level={opt}", "-o", str(out), str(src)]
    if backend:
        cmd[3:3] = [f"-Zcodegen-backend={backend}", "-Ztrust-ir-cg-args=no-proof-certs",
                    *[f"-Ztrust-ir-cg-args={k}" for k in extra]]
    env = {k: v for k, v in os.environ.items() if not k.startswith(("TCG_", "TRUST_CG_"))}
    env["XDG_CACHE_HOME"] = str(cache)
    l = load1()
    p = subprocess.run(cmd, capture_output=True, text=True, env=env)
    d = parse_time(p.stderr)
    d["load"] = l
    d["exit"] = p.returncode
    d["stderr"] = p.stderr
    return d

def med(xs):
    xs = [x for x in xs if x is not None]
    return statistics.median(xs) if xs else None

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--driver", required=True)
    ap.add_argument("--backend", action="append", required=True, metavar="NAME=DYLIB")
    ap.add_argument("--progs", type=Path, required=True)
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--n", type=int, default=3)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--no-trace", action="store_true")
    a = ap.parse_args()
    backends = dict(b.split("=", 1) for b in a.backend)
    a.work.mkdir(parents=True, exist_ok=True, mode=0o700)
    outdir = a.work / "o"; outdir.mkdir(exist_ok=True)
    caches = {}
    for n in backends:
        c = a.work / f"cache-{n}"; c.mkdir(exist_ok=True, mode=0o700); os.chmod(c, 0o700); caches[n] = c
    progs = sorted(p for p in a.progs.glob("*.rs") if not a.only or p.stem in a.only)
    report = {"backends": backends, "n": a.n, "programs": {}}
    for src in progs:
        rows = {"llvm_o2": []}
        rows.update({n: [] for n in backends})
        for n, b in backends.items():
            for _ in range(2):
                run(a, src, b, 3, caches[n], outdir / f"{src.stem}-{n}")
        for i in range(a.n):
            order = list(backends.items()) if i % 2 == 0 else list(reversed(backends.items()))
            rows["llvm_o2"].append(run(a, src, None, 2, caches[next(iter(backends))], outdir / f"{src.stem}-llvm"))
            for n, b in order:
                rows[n].append(run(a, src, b, 3, caches[n], outdir / f"{src.stem}-{n}"))
        trace = {}
        if not a.no_trace:
            for n, b in backends.items():
                r = run(a, src, b, 3, caches[n], outdir / f"{src.stem}-{n}-t", extra=("time",))
                trace[n] = [l for l in r["stderr"].splitlines() if l.startswith("TCG_TIME")]
        summ = {}
        for lane, rs in rows.items():
            ok = [r for r in rs if r["exit"] == 0]
            summ[lane] = {"n": len(ok), "wall": med([r["wall"] for r in ok]), "user": med([r["user"] for r in ok]),
                          "sys": med([r["sys"] for r in ok]), "instr": med([r["instr"] for r in ok]),
                          "rss": med([r["rss"] for r in ok]), "load": [min(r["load"] for r in rs), max(r["load"] for r in rs)],
                          "fail": [r["stderr"][-400:] for r in rs if r["exit"] != 0][:1]}
        for rs in rows.values():
            for r in rs:
                r.pop("stderr", None)
        report["programs"][src.stem] = {"summary": summ, "samples": rows, "trace": trace}
        line = " ".join(f"{k}: {v['wall']}s {round((v['instr'] or 0)/1e6)}M {round((v['rss'] or 0)/1e6,1)}MB" for k, v in summ.items())
        print(src.stem, line, flush=True)
    a.out.write_text(json.dumps(report, indent=1))

main()
