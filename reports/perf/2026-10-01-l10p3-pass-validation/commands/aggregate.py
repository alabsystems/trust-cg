#!/usr/bin/env python3
"""Aggregate a TRUST_CG_PASS_VALIDATION_LOG file by pass, validator and verdict.

Each log line is `pass<TAB>validator<TAB>verdict<TAB>function<TAB>reason`
(crates/trust-cg-opt/src/pass_validation/mod.rs, `log_record`). Prints one
TSV row per (pass, validator, verdict) with its count, then totals for the
dedicated validators, the generic region check on the other passes, and the
unchanged-claim checks.
"""
import collections
import sys

DEDICATED = {
    "instruction-scheduler", "pressure-aware-scheduler", "mem-pair-formation",
    "if-convert", "late-boolean-diamond", "tiny-loop-diamond", "licm",
}


def main(path: str) -> None:
    rows = collections.Counter()
    with open(path, encoding="utf-8", errors="replace") as log:
        for line in log:
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 3:
                continue
            rows[(parts[0], parts[1], parts[2])] += 1
    print("pass\tvalidator\tverdict\tcount")
    for (name, validator, verdict), count in sorted(rows.items()):
        print(f"{name}\t{validator}\t{verdict}\t{count}")
    totals = collections.Counter()
    for (name, validator, verdict), count in rows.items():
        if validator == "unchanged-claim":
            group = "unchanged-claim"
        elif name in DEDICATED:
            group = "dedicated"
        elif validator == "none":
            group = "uncovered"
        else:
            group = "generic-region"
        totals[(group, verdict)] += count
    print()
    print("group\tverdict\tcount")
    for (group, verdict), count in sorted(totals.items()):
        print(f"{group}\t{verdict}\t{count}")


if __name__ == "__main__":
    main(sys.argv[1])
