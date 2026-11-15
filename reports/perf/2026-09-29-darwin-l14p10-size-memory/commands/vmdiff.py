#!/usr/bin/env python3
"""Compare two `vmmap -wide` captures, excluding dyld-shared-cache regions
(nested pmap pages that ru_maxrss does not count): resident and dirty MB by
(region type, mapped file)."""
import re
import sys
from collections import defaultdict

UNIT = {"K": 1, "M": 1024, "G": 1024 * 1024}
LINE = re.compile(r"^(.+?)\s+([0-9a-f]+)-([0-9a-f]+)\s+\[\s*([\d.]+[KMG])\s+([\d.]+[KMG])\s+([\d.]+[KMG])\s+([\d.]+[KMG])\]\s+(\S+)\s+(SM=\S+)\s*(.*)$")
SHARED = ("/System/", "/usr/lib/", "dyld shared cache", "/Library/Apple/")


def kb(v):
    return float(v[:-1]) * UNIT[v[-1]]


def summarize(path):
    agg = defaultdict(lambda: [0.0, 0.0])
    for line in open(path, errors="replace"):
        if line.startswith("==== Legend"):
            break
        m = LINE.match(line.rstrip("\n"))
        if not m:
            continue
        rtype, detail = m.group(1).strip(), m.group(10).strip()
        if any(s in detail for s in SHARED) or "SM=SHM" in m.group(9) and rtype.startswith("__"):
            continue
        if rtype.startswith("MALLOC"):
            rtype, detail = "MALLOC*", ""
        elif "/" in detail:
            detail = detail.split("/")[-1]
        elif rtype.startswith("Stack"):
            detail = ""
        agg[(rtype, detail[:40])][0] += kb(m.group(5))
        agg[(rtype, detail[:40])][1] += kb(m.group(6))
    return agg


a, b = summarize(sys.argv[1]), summarize(sys.argv[2])
keys = sorted(set(a) | set(b), key=lambda k: -abs(b[k][0] - a[k][0]))
print(f"{'A res':>8} {'B res':>8} {'B-A':>8}   {'A dirty':>8} {'B dirty':>8}")
print(f"{sum(v[0] for v in a.values())/1024:8.1f} {sum(v[0] for v in b.values())/1024:8.1f} "
      f"{(sum(v[0] for v in b.values()) - sum(v[0] for v in a.values()))/1024:8.1f}   "
      f"{sum(v[1] for v in a.values())/1024:8.1f} {sum(v[1] for v in b.values())/1024:8.1f}  TOTAL (non-shared-cache)")
for k in keys[:int(sys.argv[3]) if len(sys.argv) > 3 else 25]:
    print(f"{a[k][0]/1024:8.1f} {b[k][0]/1024:8.1f} {(b[k][0]-a[k][0])/1024:8.1f}   "
          f"{a[k][1]/1024:8.1f} {b[k][1]/1024:8.1f}  {k[0]:26} {k[1]}")
