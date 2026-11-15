#!/usr/bin/env python3
"""Maintain the AArch64 closure ledger's per-gap status lines.

The ledger (docs/aarch64-completion-audit-2026-09-17.md) indexes every gap in
its gap index table and gives it a `### <ID> <title>` section whose first line,
`Status: <STATUS>`, is the gap's only status record. `counts` totals those
lines on demand; the ledger does not restate totals. The tool edits status text
only; it never decides that a gap closed.

    closure_ledger.py counts
    closure_ledger.py set <ID> <STATUS> [--note TEXT]
    closure_ledger.py add <ID> --row ROW --platform P --effort E --category C
                          --title TITLE --description TEXT [--evidence TEXT ...]

STATUS is `OPEN`, `PARTIAL <commit>`, `CLOSED <commit>` or `WITHDRAWN <commit>`.
A CLOSED or WITHDRAWN status requires a commit that exists in this repository.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "docs" / "aarch64-completion-audit-2026-09-17.md"
STATUSES = ("OPEN", "PARTIAL", "CLOSED", "WITHDRAWN")
GAP_ID = re.compile(r"^(?:L\d{2}-P\d+|C-\d{2}|X-[A-Z]+-P\d+)$")
ADDED_HEADING = "## Gaps recorded after the audit"


def counts(text: str) -> dict[str, int]:
    found = re.findall(r"^Status: (OPEN|PARTIAL|CLOSED|WITHDRAWN)\b", text, re.M)
    return {status: found.count(status) for status in STATUSES}


def check_status(status: str) -> None:
    parts = status.split(maxsplit=1)
    if not parts or parts[0] not in STATUSES:
        raise SystemExit(f"closure_ledger: status must start with one of {STATUSES}")
    if parts[0] in ("CLOSED", "WITHDRAWN", "PARTIAL"):
        if len(parts) < 2:
            raise SystemExit(f"closure_ledger: {parts[0]} needs a commit")
        commit = parts[1].split()[0]
        probe = subprocess.run(["git", "-C", str(ROOT), "cat-file", "-e", f"{commit}^{{commit}}"],
                               capture_output=True)
        if probe.returncode != 0:
            raise SystemExit(f"closure_ledger: {commit} is not a commit in this repository")


def set_status(text: str, gap: str, status: str, note: str | None) -> str:
    check_status(status)
    # The status line may end in a Markdown hard break ("  ") before a
    # Platform line, and may carry one Note line; both are preserved/replaced.
    section = re.compile(
        rf"^(### {re.escape(gap)} [^\n]*\n\n)Status: [^\n]*?(?:  \nNote: [^\n]*?)?(?P<trail> *)(?=\n)",
        re.M)
    if len(section.findall(text)) != 1:
        raise SystemExit(f"closure_ledger: expected exactly one section for {gap}")
    body = f"Status: {status}" + (f"  \nNote: {note}" if note else "")
    return section.sub(lambda match: match.group(1) + body + match.group("trail"), text, count=1)


def add_gap(text: str, args: argparse.Namespace) -> str:
    if not GAP_ID.match(args.id):
        raise SystemExit(f"closure_ledger: {args.id} is not a ledger gap id")
    if re.search(rf"^### {re.escape(args.id)} ", text, re.M):
        raise SystemExit(f"closure_ledger: {args.id} already exists")
    for value in (args.title, args.row):
        if "|" in value or "\n" in value:
            raise SystemExit("closure_ledger: titles and rows must be single-line without '|'")
    index_rows = list(re.finditer(r"^\| (?:L\d{2}-P\d+|C-\d{2}|X-[A-Z]+-P\d+) \|[^\n]*\n", text, re.M))
    if not index_rows:
        raise SystemExit("closure_ledger: gap index table not found")
    last = index_rows[-1]
    row = f"| {args.id} | {args.row} | {args.platform} | {args.effort} | {args.title} |\n"
    text = text[: last.end()] + row + text[last.end():]
    section = [f"\n### {args.id} {args.title}\n", "Status: OPEN  ",
               f"Platform: {args.platform} · Effort: {args.effort} · Category: {args.category}\n",
               args.description.strip() + "\n", "Evidence:"]
    section += [f"- {item}" for item in args.evidence] or ["- (none recorded)"]
    block = "\n".join(section) + "\n"
    if ADDED_HEADING not in text:
        refuted = text.find("\n## Refuted claims")
        intro = (f"\n{ADDED_HEADING}\n\nGaps found after the 2026-09-17 audit, with the same "
                 "evidence rules. Their IDs continue the owning row's numbering.\n")
        text = text[:refuted] + intro + text[refuted:] if refuted >= 0 else text + intro
    anchor = text.find("\n## Refuted claims")
    return text[:anchor] + block + text[anchor:] if anchor >= 0 else text + block


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--ledger", type=Path, default=LEDGER)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("counts")
    setter = sub.add_parser("set")
    setter.add_argument("id")
    setter.add_argument("status")
    setter.add_argument("--note")
    adder = sub.add_parser("add")
    adder.add_argument("id")
    for name in ("row", "platform", "effort", "category", "title", "description"):
        adder.add_argument(f"--{name}", required=True)
    adder.add_argument("--evidence", action="append", default=[])
    args = parser.parse_args(argv)
    text = args.ledger.read_text(encoding="utf-8")
    if args.command == "counts":
        print(counts(text))
        return 0
    if args.command == "set":
        if args.note and "\n" in args.note:
            raise SystemExit("closure_ledger: a note must be one line")
        text = set_status(text, args.id, args.status, args.note)
    else:
        text = add_gap(text, args)
    args.ledger.write_text(text, encoding="utf-8")
    print(counts(text))
    return 0


if __name__ == "__main__":
    sys.exit(main())
