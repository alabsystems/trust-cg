#!/usr/bin/env python3
"""Paired before/after measurement of bridge compiles on the scaling shapes:
compile-scaling's generator (blocks, loops, funcs, arraysize; -O2,
no-proof-certs + refine-solver=0, codegen-units=1, as its harness) and
scale_gate's crates (-O3, no-proof-certs). Lanes LLVM, base dylib and head
dylib run interleaved; every compile runs under /usr/bin/time -l and records
instructions retired, CPU time (user+sys), peak RSS and wall time, with the
1-minute load read before it. Linked binaries of base and head are compared
byte for byte. Measurement only.

Usage: bridge_ladder.py BASE_DYLIB HEAD_DYLIB OUT.json [--n N] [--sets compile-scaling,scale-gate]
Environment: TRUST_PKG, L14_CHECKOUT, L14_WORK.
"""
import argparse, importlib.util, json, os, re, statistics, subprocess, sys, time

PKG = os.environ["TRUST_PKG"]
W = os.environ["L14_CHECKOUT"]
S = os.environ["L14_WORK"]
RUSTC = f"{PKG}/bin/trustc"


def load_scale_gate_generate():
    sys.path.insert(0, f"{W}/benchmarks/beat-llvm")
    spec = importlib.util.spec_from_file_location("sg", f"{W}/benchmarks/beat-llvm/scale_gate.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.generate


def timed(cmd, env):
    load = os.getloadavg()[0]
    t0 = time.monotonic()
    r = subprocess.run(["/usr/bin/time", "-l", *cmd], capture_output=True, text=True, env=env)
    wall = time.monotonic() - t0
    err = r.stderr
    def num(pat, conv=int):
        m = re.search(pat, err, re.M)
        return conv(m.group(1)) if m else None
    return {
        "rc": r.returncode, "wall_s": wall, "load": load,
        "instructions": num(r"(\d+)\s+instructions retired"),
        "rss": num(r"(\d+)\s+maximum resident set size"),
        "user_s": num(r"([\d.]+) user", float), "sys_s": num(r"([\d.]+) sys", float),
        "err": err[-600:] if r.returncode else "",
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("base")
    ap.add_argument("head")
    ap.add_argument("out")
    ap.add_argument("--n", type=int, default=3)
    ap.add_argument("--sets", default="compile-scaling,scale-gate")
    ap.add_argument("--only", default=None, help="comma list of shape names")
    a = ap.parse_args()
    env = {k: v for k, v in os.environ.items() if not k.startswith(("TCG_", "TRUST_CG_"))}
    cache = f"{S}/ladder-cache"
    os.makedirs(cache, mode=0o700, exist_ok=True)
    env["XDG_CACHE_HOME"] = cache
    work = f"{S}/ladder-work"
    os.makedirs(work, exist_ok=True)
    cases = []
    if "compile-scaling" in a.sets:
        sizes = {"blocks": [100, 200, 400, 800], "loops": [15, 30, 60, 120],
                 "funcs": [50, 100, 200, 400], "arraysize": [4096, 16384, 65536, 262144]}
        base_flags = ["--edition=2021", "--crate-type", "bin", "-Cpanic=abort", "-Coverflow-checks=off",
                      "-Ccodegen-units=1", "-Cdefault-linker-libraries=y", "-Copt-level=2"]
        knobs = ["-Ztrust-ir-cg-args=no-proof-certs", "-Ztrust-ir-cg-args=refine-solver=0"]
        for shape, ns in sizes.items():
            for n in ns:
                name = f"cs-{shape}-{n}"
                if a.only and shape not in a.only.split(","):
                    continue
                src = f"{work}/{name}.rs"
                text = subprocess.run([sys.executable, f"{W}/benchmarks/compile-scaling/gen.py", shape, str(n)],
                                      capture_output=True, text=True, check=True).stdout
                open(src, "w").write(text)
                cases.append((name, src, base_flags, knobs))
    if "scale-gate" in a.sets:
        generate = load_scale_gate_generate()
        flags = ["--edition=2021", "--crate-type", "bin", "--target", "aarch64-apple-darwin",
                 "-Cpanic=abort", "-Copt-level=3"]
        for size, nfn in (("small", 25), ("medium", 200), ("large", 800), ("xlarge", 2400)):
            if a.only and size not in a.only.split(","):
                continue
            name = f"sg-{size}"
            src = f"{work}/{name}.rs"
            open(src, "w").write(generate(nfn))
            cases.append((name, src, flags, ["-Ztrust-ir-cg-args=no-proof-certs"]))
    results = {"base": a.base, "head": a.head, "n": a.n, "cases": {}}
    for name, src, flags, knobs in cases:
        samples = {"llvm": [], "base": [], "head": []}
        same = None
        for i in range(a.n):
            order = ["llvm", "base", "head"] if i % 2 == 0 else ["head", "base", "llvm"]
            for lane in order:
                os.makedirs(f"{work}/{lane}", exist_ok=True)
                out = f"{work}/{lane}/{name}"
                cmd = [RUSTC, "-Ztrust-verify=off"]
                if lane != "llvm":
                    cmd += [f"-Zcodegen-backend={a.base if lane == 'base' else a.head}", *knobs]
                cmd += [*flags, "-o", out, src]
                samples[lane].append(timed(cmd, env))
            if same is None and all(s[-1]["rc"] == 0 for s in samples.values()):
                same = open(f"{work}/base/{name}", "rb").read() == open(f"{work}/head/{name}", "rb").read()
        med = {}
        for lane, rows in samples.items():
            ok = [r for r in rows if r["rc"] == 0]
            if not ok:
                med[lane] = {"failed": rows[0]["err"]}
                continue
            m = lambda k: statistics.median(r[k] for r in ok)
            med[lane] = {"instructions_G": round(m("instructions") / 1e9, 3),
                         "cpu_s": round(statistics.median(r["user_s"] + r["sys_s"] for r in ok), 3),
                         "rss_MiB": round(m("rss") / 2**20, 1), "wall_s": round(m("wall_s"), 3),
                         "load_min": round(min(r["load"] for r in ok), 2),
                         "load_max": round(max(r["load"] for r in ok), 2)}
        results["cases"][name] = {"medians": med, "base_head_binaries_identical": same, "samples": samples}
        b, h, l = med.get("base", {}), med.get("head", {}), med.get("llvm", {})
        print(f"{name:18s} llvm {l.get('instructions_G')}G {l.get('cpu_s')}s {l.get('rss_MiB')}MiB | "
              f"base {b.get('instructions_G')}G {b.get('cpu_s')}s {b.get('rss_MiB')}MiB | "
              f"head {h.get('instructions_G')}G {h.get('cpu_s')}s {h.get('rss_MiB')}MiB | "
              f"identical={same} load {h.get('load_min')}-{h.get('load_max')}", flush=True)
        json.dump(results, open(a.out, "w"), indent=1)


main()
