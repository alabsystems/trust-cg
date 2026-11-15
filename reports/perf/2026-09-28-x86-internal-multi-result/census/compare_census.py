#!/usr/bin/env python3
"""Compare two x86_retarget_census outputs (base, new).

Every (module, triple, level) row must be byte-identical (same verdict, same
object SHA-256 and length, same refusal text) EXCEPT rows whose base refusal is
the x86-64 selector's register-capacity refusal, which the internal
multi-result convention is meant to turn into compiled objects. Prints a
summary and exits 1 on any other difference.
"""
import collections
import sys

CAPACITY = "result register capacity is exhausted"


def load(path):
    rows = {}
    for line in open(path):
        parts = line.rstrip("\n").split(" ", 4)
        key = tuple(parts[:3])
        rows[key] = (parts[3], parts[4] if len(parts) > 4 else "")
    return rows


def origin(module):
    # modules/<origin>/<name>
    parts = module.split("/")
    return parts[1] if len(parts) > 2 else module


def main(base_path, new_path):
    base, new = load(base_path), load(new_path)
    if set(base) != set(new):
        print("ROW SETS DIFFER", len(base), len(new))
        return 1
    stats = collections.Counter()
    by_origin = collections.Counter()
    bad = []
    newly = collections.Counter()
    for key in sorted(base):
        b, n = base[key], new[key]
        o = origin(key[0])
        stats[("base", b[0])] += 1
        stats[("new", n[0])] += 1
        if b == n:
            by_origin[(o, "identical-" + b[0])] += 1
            continue
        if b[0] == "err" and CAPACITY in b[1]:
            newly[(o, n[0], n[1] if n[0] == "err" else "")] += 1
            by_origin[(o, "capacity->" + n[0])] += 1
            continue
        bad.append((key, b, n))
    print("rows:", len(base))
    for k in sorted(stats):
        print("  %-4s %-3s %6d" % (k[0], k[1], stats[k]))
    print("by origin:")
    for k in sorted(by_origin):
        print("  %-12s %-22s %6d" % (k[0], k[1], by_origin[k]))
    print("capacity refusals in base, now:")
    for k in sorted(newly):
        print("  %-12s %-3s %6d %s" % (k[0], k[1], newly[k], k[2][:160]))
    print("OTHER DIFFERENCES:", len(bad))
    for key, b, n in bad[:20]:
        print("  ", key, b, "->", n)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2]))
