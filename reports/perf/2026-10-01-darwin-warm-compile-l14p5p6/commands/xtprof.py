#!/usr/bin/env python3
"""Aggregate an `xctrace export` time-profile table: per-thread sample counts,
top self frames and inclusive frames, optionally inside a time window and for
one thread. Testing evidence only."""
import argparse, collections, re, sys
import xml.etree.ElementTree as ET

def load(path):
    tree = ET.parse(path)
    root = tree.getroot()
    ids = {}
    for el in root.iter():
        i = el.get("id")
        if i is not None:
            ids[i] = el
    def deref(el):
        r = el.get("ref")
        return ids[r] if r is not None else el
    rows = []
    for row in root.iter("row"):
        t = th = st = None
        weight = 1.0
        stack = []
        for c in row:
            c = deref(c)
            if c.tag == "sample-time":
                t = int(c.text) / 1e6
            elif c.tag == "thread":
                th = c.get("fmt")
            elif c.tag == "thread-state":
                st = c.get("fmt")
            elif c.tag == "weight":
                weight = int(c.text) / 1e6
            elif c.tag in ("tagged-backtrace", "backtrace"):
                for f in c.iter("frame"):
                    f = deref(f)
                    stack.append(f.get("name"))
        rows.append((t, th, st, weight, stack))
    return rows

def rough_v0(name):
    # Rough Rust v0 demangle: collect length-prefixed identifiers.
    if not name.startswith("_R"):
        return name
    out = []
    i = 2
    s = name
    while i < len(s):
        m = re.match(r"(\d+)_?", s[i:])
        if m and m.group(1) != "0":
            n = int(m.group(1)); j = i + len(m.group(0))
            ident = s[j:j+n]
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", ident or "-"):
                out.append(ident); i = j + n; continue
        i += 1
    keep = [x for x in out if not re.fullmatch(r"(core|std|alloc|ops|function|FnOnce|call_once|closure|h[0-9a-f]+)", x)]
    return "::".join(keep[-5:]) or name[:60]

def norm(name):
    name = re.sub(r"::h[0-9a-f]{16}$", "", name or "?")
    return rough_v0(name)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("xml")
    ap.add_argument("--thread", default=None, help="substring of the thread label")
    ap.add_argument("--t0", type=float, default=None, help="ms")
    ap.add_argument("--t1", type=float, default=None, help="ms")
    ap.add_argument("--top", type=int, default=40)
    ap.add_argument("--incl", default=None, help="regex: only stacks containing a matching frame")
    a = ap.parse_args()
    rows = load(a.xml)
    per_thread = collections.Counter()
    for t, th, st, w, stack in rows:
        per_thread[th] += w
    print("threads:")
    for th, n in per_thread.most_common(12):
        print(f"  {n:8.1f} ms  {th}")
    sel = [r for r in rows if (a.thread is None or (r[1] and a.thread in r[1]))
           and (a.t0 is None or r[0] >= a.t0) and (a.t1 is None or r[0] <= a.t1)]
    if a.incl:
        rx = re.compile(a.incl)
        sel = [r for r in sel if any(rx.search(norm(f)) for f in r[4])]
    total = sum(r[3] for r in sel)
    selfc = collections.Counter(); inc = collections.Counter()
    for t, th, st, w, stack in sel:
        if stack:
            selfc[norm(stack[0])] += w
        for f in set(norm(f) for f in stack):
            inc[f] += w
    print(f"selected {total:.1f} ms")
    print("self:")
    for f, n in selfc.most_common(a.top):
        print(f"  {n:8.1f} {100*n/max(total,1e-9):5.1f}%  {f[:160]}")
    print("inclusive:")
    for f, n in inc.most_common(a.top):
        print(f"  {n:8.1f} {100*n/max(total,1e-9):5.1f}%  {f[:160]}")

main()
