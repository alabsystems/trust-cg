#!/usr/bin/env python3
# Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
"""Extract every replayed outcome from a `--lib _qualification` log.

    python3 -I outcomes.py <run.log> <out.tsv>

Reads the lanes' own `X86_BODY_*QUALIFICATION shape=<label> [part=<k>]
result=<AYResult> ms=<n>` lines (and the slice-9 `SPELLING` lines), keyed by
the test that printed them, and writes one TSV row per replay: test, label,
class (`Verified`, `Timeout`, `checker-rejected`, `self-check-rejected`,
`CounterExample`, or the outcome itself), milliseconds and the outcome with
paths elided. Then prints each test's verdict line and its counts.
"""

from __future__ import annotations

import collections
import re
import sys

TEST = re.compile(r"^test (\S+) \.\.\. ")
VERDICT = re.compile(r"^test (\S+) \.\.\. (ok|FAILED|ignored)$")
REPLAY = re.compile(
    r"^X86_BODY_(?P<lane>\w*?)_?(?:QUALIFICATION|SPELLING) (?:shape=(?P<shape>.*?) )?"
    r"(?:part=(?P<part>\S+) )?(?:rows=\d+ )?(?:spelling=(?P<spelling>\S+) )?result=(?P<result>.*) ms=(?P<ms>\d+)$"
)
PATH = re.compile(r"/[^\s\"]*")


def classify(result: str) -> str:
    if result == "Verified":
        return "Verified"
    if result.startswith("Timeout"):
        return "Timeout"
    if result.startswith("CounterExample"):
        return "CounterExample"
    if "working checker" in result:
        return "checker-rejected"
    if "self-check-rejected" in result:
        return "self-check-rejected"
    return PATH.sub("<path>", result)


def main() -> int:
    log, out = sys.argv[1], sys.argv[2]
    test = "?"
    counts: dict[str, collections.Counter] = collections.OrderedDict()
    verdicts: dict[str, str] = {}
    with open(log, errors="replace") as handle, open(out, "w") as tsv:
        tsv.write("test\tlabel\tclass\tms\toutcome\n")
        for raw in handle:
            line = raw.rstrip("\n")
            started = TEST.match(line)
            if started:
                test = started.group(1).replace("x86_source_bound_body::tests::", "")
            done = VERDICT.match(line)
            if done:
                verdicts[done.group(1).replace("x86_source_bound_body::tests::", "")] = done.group(2)
            if line in ("ok", "FAILED") or line.endswith(" ok") or line.endswith("FAILED"):
                if test != "?" and test not in verdicts:
                    verdicts[test] = "ok" if line.endswith("ok") else "FAILED"
            replay = REPLAY.match(line.strip())
            if not replay:
                continue
            label = replay.group("shape") or ""
            if replay.group("part"):
                label += f" part {replay.group('part')}"
            if replay.group("spelling"):
                label += f" spelling={replay.group('spelling')}"
            result = replay.group("result")
            kind = classify(result)
            counts.setdefault(test, collections.Counter())[kind] += 1
            tsv.write(f"{test}\t{label}\t{kind}\t{replay.group('ms')}\t{PATH.sub('<path>', result)}\n")
    for name in sorted(set(counts) | set(verdicts)):
        print(f"{verdicts.get(name, '?'):7} {name} {dict(counts.get(name, {}))}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
