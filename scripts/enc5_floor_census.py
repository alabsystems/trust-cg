#!/usr/bin/env python3
"""Reduce an ENC-5 emission census into the committed, test-pinned census.

Measure: run the Darwin floor with the census sink enabled, for example

    TCG_DECODE_CHECK_CENSUS_DIR=/tmp/enc5 \\
        python3 scripts/check_darwin_aarch64.py --out /tmp/floor

(the pipeline appends /tmp/enc5/enc5-<pid>.tsv per process; see
crates/trust-cg-codegen/src/aarch64/decode_census.rs), then reduce:

    python3 scripts/enc5_floor_census.py /tmp/enc5 --floor-report \\
        /tmp/floor/report.json --out \\
        crates/trust-cg-codegen/tests/aarch64_enc5_floor_census/darwin_floor.tsv

The output keeps, per opcode: the instruction tally by integrity policy,
ENC-5 outcome and allowlist reason; the floor test binaries that emitted it;
and a bounded, deterministic set of distinct real samples (operands, fixup
hole, emitted word) that tests/aarch64_enc5_floor_census.rs replays through
ENC-5. A census is testing evidence about which forms a corpus reached. Like
every TCG_* variable the sink makes artifact reuse ineligible, so tests that
require an environment without compiler controls fail while it is set; the
reduced header names the floor targets that did not pass.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

SAMPLES_PER_CLASS = 6
HASH_SUFFIX = re.compile(r"-[0-9a-f]{16}$")


def target_name(exe: str) -> str:
    return HASH_SUFFIX.sub("", Path(exe).name) if exe else "?"


def reduce(census_dir: Path) -> tuple[dict, dict, dict, int]:
    tallies: dict[tuple[str, str, str, str], int] = defaultdict(int)
    samples: dict[tuple[str, str, str, str], set[tuple[str, str, str]]] = defaultdict(set)
    emitters: dict[str, set[str]] = defaultdict(set)
    files = sorted(census_dir.glob("enc5-*.tsv"))
    for path in files:
        target = "?"
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            fields = line.split("\t")
            if fields[0] == "P" and len(fields) >= 3:
                target = target_name(fields[2])
            elif fields[0] == "T" and len(fields) == 6:
                _, opcode, policy, outcome, reason, count = fields
                tallies[(opcode, policy, outcome, reason)] += int(count)
                emitters[opcode].add(target)
            elif fields[0] == "S" and len(fields) == 8:
                _, opcode, policy, outcome, reason, word, hole, operands = fields
                samples[(opcode, policy, outcome, reason)].add((word, hole, operands))
    return tallies, samples, emitters, len(files)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("census_dir", type=Path)
    parser.add_argument("--floor-report", type=Path, help="the census run's floor report.json")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    tallies, samples, emitters, processes = reduce(args.census_dir)
    if not tallies:
        print(f"no census records under {args.census_dir}", file=sys.stderr)
        return 1
    header = [
        "# ENC-5 emission census of the Darwin AArch64 floor (testing evidence, not proof).",
        "# Reduced by scripts/enc5_floor_census.py from TCG_DECODE_CHECK_CENSUS_DIR output.",
        f"# processes: {processes}",
    ]
    if args.floor_report:
        report = json.loads(args.floor_report.read_text(encoding="utf-8"))
        provenance = report.get("provenance", {})
        header.append(f"# source: {provenance.get('source_sha', '?')} dirty={provenance.get('dirty', '?')}")
        header.append(f"# host: {report.get('host', '?')}")
        header.append(f"# floor status: {report.get('status', '?')}; targets run: {len(report.get('targets', []))}")
        failed = sorted(f"{row['package']}/{row['target']}" for row in report.get("targets", [])
                        if row.get("status") != "pass")
        header.append(f"# targets not passing in the census run: {', '.join(failed) if failed else 'none'}")
    header.append("# T opcode policy outcome reason count | E opcode targets | S opcode policy outcome reason word hole operands")
    lines = list(header)
    for key in sorted(tallies):
        lines.append("\t".join(("T", *key, str(tallies[key]))))
    for opcode in sorted(emitters):
        lines.append("\t".join(("E", opcode, ",".join(sorted(emitters[opcode])))))
    for key in sorted(samples):
        # Deterministic spread: the distinct samples in sorted order, taken at
        # an even stride so register and immediate diversity survives.
        distinct = sorted(samples[key])
        stride = max(1, len(distinct) // SAMPLES_PER_CLASS)
        for word, hole, operands in distinct[::stride][:SAMPLES_PER_CLASS]:
            lines.append("\t".join(("S", *key, word, hole, operands)))
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text("\n".join(lines) + "\n", encoding="utf-8")
    opcodes = {key[0] for key in tallies}
    allowlisted = sorted({key[0] for key in tallies if key[2] == "allowlisted"})
    print(f"{len(opcodes)} opcodes emitted; {len(allowlisted)} with allowlisted outcomes: {' '.join(allowlisted)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
