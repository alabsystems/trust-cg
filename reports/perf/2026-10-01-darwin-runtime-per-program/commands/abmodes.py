#!/usr/bin/env python3
# Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
"""abmodes.py <binary> <rounds> <mode>...: run `<binary> <mode>` for every mode
once per round in a rotated order under /usr/bin/time -l; print cycles and
instructions retired (min / median) per mode, the ratio to the first mode,
and the 1-minute load range."""
import re, statistics, subprocess, sys
binary, rounds, modes = sys.argv[1], int(sys.argv[2]), sys.argv[3:]
def load1():
    return float(subprocess.run(["sysctl", "-n", "vm.loadavg"], capture_output=True, text=True).stdout.strip("{} \n").split()[0])
res = {m: {"c": [], "i": []} for m in modes}
loads = []
for r in range(rounds + 1):
    loads.append(load1())
    order = modes[r % len(modes):] + modes[:r % len(modes)]
    for m in order:
        e = subprocess.run(["/usr/bin/time", "-l", binary, m], capture_output=True, text=True).stderr
        if r == 0:
            continue
        res[m]["c"].append(int(re.search(r"(\d+)\s+cycles elapsed", e).group(1)))
        res[m]["i"].append(int(re.search(r"(\d+)\s+instructions retired", e).group(1)))
b = res[modes[0]]
for m in modes:
    c, i = res[m]["c"], res[m]["i"]
    print(f"{m:6} cyc_min {min(c)/1e6:9.2f}M ({min(c)/min(b['c']):.3f}) cyc_med {statistics.median(c)/1e6:9.2f}M "
          f"({statistics.median(c)/statistics.median(b['c']):.3f}) ins {statistics.median(i)/1e6:9.2f}M")
print(f"load {min(loads):.1f}-{max(loads):.1f}")
