#!/usr/bin/env python3
"""Summarize ladder .time files (bridge) into a TSV: size, instructions
retired, max RSS (bytes), wall, 1-minute load, and the CGU phase line.
Usage: summarize.py <ladder-dir> <out.tsv>"""
import re
import sys
from pathlib import Path

SIZES = ["small", "x100", "medium", "x400", "large", "x1600", "xlarge"]
LINES = {"small": 355, "x100": 1405, "medium": 2805, "x400": 5605, "large": 11205,
         "x1600": 22405, "xlarge": 33605}
FNS = {"small": 25, "x100": 100, "medium": 200, "x400": 400, "large": 800, "x1600": 1600,
       "xlarge": 2400}
d = Path(sys.argv[1])
rows = ["crate\tfunctions\tlines\tinstructions_retired\tmax_rss_bytes\twall_s\tload1\tphases"]
for name in SIZES:
    f = d / f"{name}.time"
    if not f.exists():
        continue
    t = f.read_text()
    ins = re.search(r"(\d+)\s+instructions retired", t).group(1)
    rss = re.search(r"(\d+)\s+maximum resident set size", t).group(1)
    wall = re.search(r"([\d.]+) real", t).group(1)
    load = re.search(r"load: \{ ([\d.]+)", t).group(1)
    m = re.search(rf"TCG_TIME cgu={name}\.\S+ (.*)", t)
    phases = m.group(1) if m else ""
    rows.append(f"{name}\t{FNS[name]}\t{LINES[name]}\t{ins}\t{rss}\t{wall}\t{load}\t{phases}")
Path(sys.argv[2]).write_text("\n".join(rows) + "\n")
print("\n".join(r.split("\t", 7)[0:7].__str__() for r in rows))
