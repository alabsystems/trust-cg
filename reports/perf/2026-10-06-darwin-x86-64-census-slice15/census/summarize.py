#!/usr/bin/env python3
"""Summarize a probe dump: one line per function (LIR instructions and blocks,
machine rows, the verdict). usage: summarize.py <dump> [names file]"""
import re, sys

dump = open(sys.argv[1]).read().split("\n==== ")
names = None
if len(sys.argv) > 2:
    names = {re.sub(r'^__trust_cg_private\.[^.]+\.[^.]+\.[0-9]+\.[0-9]+\.', '', l.strip())
             for l in open(sys.argv[2]) if l.strip()}
for chunk in dump:
    chunk = chunk.lstrip("= ")
    if not chunk.strip():
        continue
    lines = chunk.split("\n")
    name = lines[0].strip()
    if names is not None and name not in names:
        continue
    lir = sum(1 for l in lines if re.match(r"^    \[", l))
    blocks = sum(1 for l in lines if re.match(r"^  Block\(", l))
    rows = sum(1 for l in lines if re.match(r"^ +\d+ [A-Z]", l))
    body = next((l.strip() for l in lines if l.strip().startswith("BODY")), "?")
    body = body.replace("unsupported source-bound x86-64 body: ", "").replace("BODY ", "")
    print(f"{name[:90]}\tlir={lir}\tblocks={blocks}\trows={rows}\t{body[:220]}")
