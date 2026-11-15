#!/usr/bin/env python3
"""For each function of a class file (split_classes.py): LIR block count, whether
the CFG has a loop, the number of entry-to-end paths and the longest path in
instructions (the slice-6 bounds: 16 blocks, 16 paths, 256 instructions).
Usage: cfg_scan.py <cls_file>..."""
import re
import sys
from functools import lru_cache

for path in sys.argv[1:]:
    fns = {}
    cur = None
    block = None
    for line in open(path, errors="replace"):
        if line.startswith("==== "):
            cur = line[5:].strip()
            fns[cur] = {"blocks": {}, "entry": None}
            block = None
            continue
        if cur is None:
            continue
        m = re.match(r"^  Block\((\d+)\) params", line)
        if m:
            block = int(m.group(1))
            fns[cur]["blocks"][block] = {"n": 0, "succ": []}
            if fns[cur]["entry"] is None:
                fns[cur]["entry"] = block
            continue
        if line.startswith("  value_types") or line.startswith("  MBlock"):
            block = None
            continue
        if block is not None and line.startswith("    ["):
            b = fns[cur]["blocks"][block]
            b["n"] += 1
            for t in re.findall(r"(?:dest|then_dest|else_dest|default): Block\((\d+)\)", line):
                b["succ"].append(int(t))
            if "Switch" in line:
                b["succ"] += [int(t) for t in re.findall(r", Block\((\d+)\)\)", line)]
    ok = 0
    for name, f in fns.items():
        blocks = f["blocks"]
        # loop detection
        colour = {}
        loop = False

        def dfs(b):
            global loop
            colour[b] = 1
            for s in blocks.get(b, {"succ": []})["succ"]:
                if colour.get(s) == 1:
                    loop = True
                elif s not in colour:
                    dfs(s)
            colour[b] = 2
        sys.setrecursionlimit(10000)
        dfs(f["entry"])
        paths = longest = None
        if not loop:
            @lru_cache(None)
            def count(b):
                succ = blocks[b]["succ"]
                return 1 if not succ else sum(count(s) for s in set(succ))

            @lru_cache(None)
            def length(b):
                succ = blocks[b]["succ"]
                return blocks[b]["n"] + (max(length(s) for s in set(succ)) if succ else 0)
            paths, longest = count(f["entry"]), length(f["entry"])
        fits = (not loop) and len(blocks) <= 16 and paths <= 16 and longest <= 256
        ok += fits
        print(f"{'OK ' if fits else '-- '} blocks={len(blocks):3d} loop={int(loop)} paths={paths} longest={longest}  {name[:100]}")
    print(f"{path}: {ok} of {len(fns)} within the slice-6 control-flow bounds")
