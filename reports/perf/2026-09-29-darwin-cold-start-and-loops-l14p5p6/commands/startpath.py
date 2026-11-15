#!/usr/bin/env python3
"""Interleaved cold (a fresh private XDG_CACHE_HOME per compile) and warm
bridge compiles of programs with two backends built with the start-path
marks. The backend's `time` knob prints `TCG_TIME start_path ...`: ms from
the process start for each step. Prints per-lane medians and stores every
raw sample. Measurement only.

Usage: startpath.py OUT.json N BEFORE_DYLIB AFTER_DYLIB PROGRAM...
Environment: TRUST_PKG (Trust package root), L14_WORK (a private work dir).
"""
import json, os, re, shutil, statistics, subprocess, sys, tempfile, time

PKG = os.environ["TRUST_PKG"]
S = os.environ["L14_WORK"]
out_path, n, before, after, *programs = sys.argv[1:]
n = int(n)
dylibs = {"before": before, "after": after}
env0 = {k: v for k, v in os.environ.items() if not k.startswith(("TCG_", "TRUST_CG_"))}
results = {"dylibs": dylibs, "n": n, "programs": {}}
warm_roots = {}
for lane in dylibs:
    root = tempfile.mkdtemp(prefix=f"warm-{lane}-", dir=S)
    os.chmod(root, 0o700)
    warm_roots[lane] = root


def compile_once(dylib, src, cache):
    cmd = ["/usr/bin/time", "-l", f"{PKG}/bin/trustc", "-Ztrust-verify=off", f"-Zcodegen-backend={dylib}",
           "-Ztrust-ir-cg-args=no-proof-certs", "-Ztrust-ir-cg-args=time", "--edition=2021",
           "--crate-type", "bin", "--target", "aarch64-apple-darwin", "-Cpanic=abort", "-Copt-level=3",
           "-o", f"{S}/sp-out", src]
    env = dict(env0, XDG_CACHE_HOME=cache)
    load = os.getloadavg()[0]
    t0 = time.monotonic()
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    wall = time.monotonic() - t0
    marks = []
    line = next((l for l in r.stderr.splitlines() if l.startswith("TCG_TIME start_path ")), "")
    for pair in line.split()[3:]:
        k, _, v = pair.partition("=")
        marks.append((k, float(v)))
    ins = re.search(r"(\d+)\s+instructions retired", r.stderr)
    cost = next((l for l in r.stderr.splitlines() if l.startswith("TCG_TIME process_cost")), "")
    return {"rc": r.returncode, "wall_s": wall, "load": load, "marks": marks, "process_cost": cost,
            "instructions": int(ins.group(1)) if ins else None}


def first(marks, key):
    return next((v for k, v in marks if k == key), None)


for src in programs:
    name = os.path.basename(src)
    for lane, dylib in dylibs.items():  # populate the warm roots
        compile_once(dylib, src, warm_roots[lane])
    rows = {f"{lane}-{kind}": [] for lane in dylibs for kind in ("cold", "warm")}
    for i in range(n):
        order = list(dylibs.items()) if i % 2 == 0 else list(reversed(list(dylibs.items())))
        for lane, dylib in order:
            cold = tempfile.mkdtemp(prefix="cold-", dir=S)
            os.chmod(cold, 0o700)
            try:
                rows[f"{lane}-cold"].append(compile_once(dylib, src, cold))
            finally:
                shutil.rmtree(cold, ignore_errors=True)
            rows[f"{lane}-warm"].append(compile_once(dylib, src, warm_roots[lane]))
    summary = {}
    for key, samples in rows.items():
        ok = [s for s in samples if s["rc"] == 0]

        def med(f):
            vals = [v for v in (f(s) for s in ok) if v is not None]
            return round(statistics.median(vals), 1) if vals else None
        summary[key] = {
            "n_ok": len(ok),
            "wall_ms": med(lambda s: s["wall_s"] * 1000),
            "wall_min_ms": round(min(s["wall_s"] for s in ok) * 1000, 1) if ok else None,
            "instructions_M": med(lambda s: s["instructions"] / 1e6 if s["instructions"] else None),
            "backend_init": med(lambda s: first(s["marks"], "backend_init")),
            "copy_published": med(lambda s: first(s["marks"], "ay_copy_published")),
            "assessment_begun": med(lambda s: first(s["marks"], "ay_assessment_begun")),
            "first_start_begin": med(lambda s: first(s["marks"], "ay_first_start_begin")),
            "first_start_end": med(lambda s: first(s["marks"], "ay_first_start_end")),
            "codegen_crate": med(lambda s: first(s["marks"], "codegen_crate")),
            "first_solve_wait": med(lambda s: (first(s["marks"], "ay_first_start_wait_end") or 0)
                                    - (first(s["marks"], "ay_first_start_wait_begin") or 0)),
            "join_codegen_end": med(lambda s: first(s["marks"], "join_codegen_end")),
            "load_min": min(s["load"] for s in samples), "load_max": max(s["load"] for s in samples),
        }
        print(name, key, json.dumps(summary[key]), flush=True)
    results["programs"][name] = {"summary": summary, "samples": rows}
    json.dump(results, open(out_path, "w"), indent=1)
for root in warm_roots.values():
    shutil.rmtree(root, ignore_errors=True)
