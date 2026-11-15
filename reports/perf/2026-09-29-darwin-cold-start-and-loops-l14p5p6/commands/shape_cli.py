#!/usr/bin/env python3
"""Interleaved before/after CLI measurement of the L14-P6 shapes: median of N
runs of instructions retired, peak RSS and wall (with the 1-minute load read
before each compile), plus object identity. Measurement only.

Usage: shape_cli.py N BASE_CLI HEAD_CLI OUT.json MODULE[:OPT]...
A `.tmbc` module is read as binary, anything else as text. Objects are
written to $L14_WORK.
"""
import json, os, re, statistics, subprocess, sys, time

n, base, head, out_json, *mods = sys.argv[1:]
n = int(n)
S = os.environ["L14_WORK"]
clis = {"base": base, "head": head}
results = []
for spec in mods:
    mod, _, opt = spec.partition(":")
    opt = opt or "-O3"
    fmt = "binary" if mod.endswith(".tmbc") else "text"
    rows = {k: [] for k in clis}
    objs = {}
    for i in range(n):
        order = list(clis.items()) if i % 2 == 0 else list(reversed(list(clis.items())))
        for tag, cli in order:
            out = f"{S}/final-{tag}.o"
            load = os.getloadavg()[0]
            t0 = time.monotonic()
            r = subprocess.run(["/usr/bin/time", "-l", cli, f"--format={fmt}", "-c", opt, "--target",
                                "aarch64-apple-darwin", "-o", out, mod], capture_output=True, text=True)
            wall = time.monotonic() - t0
            ins = re.search(r"(\d+)\s+instructions retired", r.stderr)
            rss = re.search(r"(\d+)\s+maximum resident set size", r.stderr)
            rows[tag].append({"rc": r.returncode, "instructions": int(ins.group(1)) if ins else None,
                              "max_rss": int(rss.group(1)) if rss else None, "wall_s": wall, "load": load})
            objs[tag] = open(out, "rb").read() if r.returncode == 0 else None
            if os.path.exists(out):
                os.unlink(out)
    summary = {"module": os.path.basename(mod), "opt": opt,
               "identical": objs["base"] is not None and objs["base"] == objs["head"]}
    for tag, samples in rows.items():
        summary[tag] = {
            "rc": sorted({s["rc"] for s in samples}),
            "instructions_G": round(statistics.median(s["instructions"] for s in samples) / 1e9, 3),
            "max_rss_MiB": round(statistics.median(s["max_rss"] for s in samples) / 2**20, 1),
            "wall_s": round(statistics.median(s["wall_s"] for s in samples), 3),
            "load_min": round(min(s["load"] for s in samples), 1),
            "load_max": round(max(s["load"] for s in samples), 1),
        }
    results.append({"summary": summary, "samples": rows})
    b, h = summary["base"], summary["head"]
    print(f"{summary['module']:22s} {opt} base {b['instructions_G']:8.3f}G {b['max_rss_MiB']:7.1f}MiB "
          f"{b['wall_s']:6.3f}s | head {h['instructions_G']:8.3f}G {h['max_rss_MiB']:7.1f}MiB {h['wall_s']:6.3f}s "
          f"| identical={summary['identical']} load {min(b['load_min'], h['load_min'])}-"
          f"{max(b['load_max'], h['load_max'])}", flush=True)
    json.dump(results, open(out_json, "w"), indent=1)
