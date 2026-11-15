#!/usr/bin/env python3
"""Log the load every 30 s; exit when the 1-min load < LIM1 and the 5-min load < LIM5.

Usage: wait_quiet.py <tsv> <lim1> <lim5> <max_minutes>
Exit 0 when quiet, 3 when max_minutes passed without quiet.
"""
import os
import sys
import time
from datetime import datetime, timezone

tsv, lim1, lim5, max_min = sys.argv[1], float(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
start = time.time()
new = not os.path.exists(tsv)
with open(tsv, "a") as f:
    if new:
        f.write("utc\tloadavg_1_5_15\n")
i = 0
while True:
    l1, l5, l15 = os.getloadavg()
    now = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    with open(tsv, "a") as f:
        f.write(f"{now}\t{l1:.2f} {l5:.2f} {l15:.2f}\n")
    if l1 < lim1 and l5 < lim5:
        print(f"QUIET {now} load {l1:.2f} {l5:.2f} {l15:.2f}", flush=True)
        sys.exit(0)
    if time.time() - start > max_min * 60:
        print(f"TIMEOUT {now} load {l1:.2f} {l5:.2f} {l15:.2f}", flush=True)
        sys.exit(3)
    i += 1
    if i % 10 == 0:
        print(f"waiting {now} load {l1:.2f} {l5:.2f} {l15:.2f}", flush=True)
    time.sleep(30)
