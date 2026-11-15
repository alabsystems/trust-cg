#!/usr/bin/env python3
"""Compare two one-test-per-process qualification ledgers (replay/qualify.sh out dirs).

usage: compare_ledgers.py OLD_DIR NEW_DIR [--slow-ms N]
Reads every `X86_*` outcome line each lane prints (`shape=`, `refutation=`, `encoding=`,
`spellings=`, `uf-world=`, `concatenated=`, `preserved-tail=`, `mutant=`, ...), keyed by test
log and the line up to its `result=`. A counterexample's model is compared as
`CounterExample` (its values may differ between AYs), and the `ms=` field is timing only.
Prints every key whose outcome differs or that exists in one ledger only, then every
certified case slower than --slow-ms (default 15000) in either ledger, with both times.
"""
import os
import re
import sys

CEX = re.compile(r"CounterExample\(\[.*?\]\)")


def ledger(directory):
    rows = {}
    for name in sorted(os.listdir(directory)):
        if not name.endswith(".log"):
            continue
        test = name[:-4]
        for line in open(os.path.join(directory, name), errors="replace"):
            line = line.strip()
            m = re.search(r"(X86_[A-Z0-9_]+) (.*)$", line)
            if not m or m.group(1) in ("X86_BODY_REPLAY_IDENTITY",) or "recorded tool output" in line:
                continue
            body = m.group(2)
            ms = re.search(r" ms=(\d+)", body)
            body = re.sub(r" ms=\d+", "", body)
            body = CEX.sub("CounterExample", body)
            if " result=" in body:
                key, result = body.split(" result=", 1)
            elif m.group(1).endswith("QUALIFICATION") and body.startswith("gap="):
                key, result = body.split(" ", 1)
            else:
                key, result = body, ""
            rows[(test, m.group(1), key)] = (result, int(ms.group(1)) if ms else None)
    return rows


def main():
    old, new = ledger(sys.argv[1]), ledger(sys.argv[2])
    slow = int(sys.argv[sys.argv.index("--slow-ms") + 1]) if "--slow-ms" in sys.argv else 15000
    print("== outcome changes (test | lane | case | old -> new)")
    changed = 0
    for key in sorted(set(old) | set(new)):
        a, b = old.get(key), new.get(key)
        if a is None or b is None or a[0] != b[0]:
            changed += 1
            print(f"{key[0]} | {key[1]} | {key[2]} | {a[0] if a else '(absent)'} [{a[1] if a else ''} ms] -> "
                  f"{b[0] if b else '(absent)'} [{b[1] if b else ''} ms]")
    print(f"== {changed} changed of {len(set(old) | set(new))} cases")
    print(f"== certified cases at or over {slow} ms in either ledger (old ms -> new ms)")
    for key in sorted(set(old) & set(new)):
        a, b = old[key], new[key]
        if a[0] == "Verified" and b[0] == "Verified" and a[1] is not None and b[1] is not None \
                and max(a[1], b[1]) >= slow:
            print(f"{key[0]} | {key[2]} | {a[1]} -> {b[1]}")
    for label, rows in (("old", old), ("new", new)):
        n_cex = sum(1 for v in rows.values() if v[0].startswith("CounterExample"))
        n_ver = sum(1 for v in rows.values() if v[0] == "Verified")
        print(f"== {label}: {len(rows)} cases, {n_ver} Verified, {n_cex} CounterExample")


main()
