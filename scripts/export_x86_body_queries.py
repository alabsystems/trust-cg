#!/usr/bin/env python3
"""Export canonical x86 body snapshots without changing their SMT commands.

The Rust snapshot tests bind these source fixtures to the real query builders.
This script runs no solver or checker and grants no proof credit. Additional
machine variants, wrong-lowering controls and alternative encodings remain
separate qualification obligations.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys


ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "crates/trust-cg-verify/tests/fixtures/x86_source_bound_body"
FAMILIES = {
    "body": "snapshots.smt2",
    "memory": "memory_snapshots.smt2",
    **{f"slice{n}": f"slice{n}_snapshots.smt2" for n in (5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)},
}
MARKER = re.compile(r"^;;;; ([A-Za-z0-9_]+)\n", re.MULTILINE)


def snapshot_queries(data: bytes, name: str) -> list[tuple[str, bytes]]:
    text = data.decode("utf-8")
    markers = list(MARKER.finditer(text))
    if not markers or markers[0].start() != 0:
        raise ValueError(f"{name}: missing initial fixture marker")
    queries = []
    labels = set()
    for index, marker in enumerate(markers):
        label = marker.group(1)
        if label in labels:
            raise ValueError(f"{name}: duplicate fixture {label}")
        labels.add(label)
        end = markers[index + 1].start() if index + 1 < len(markers) else len(text)
        query = text[marker.end():end].rstrip("\n")
        if not query.startswith("(set-option :timeout ") or not query.endswith("(check-sat)\n(exit)"):
            raise ValueError(f"{name}/{label}: incomplete canonical query")
        queries.append((label, query.encode("utf-8")))
    return queries


def export(out: Path, families: list[str]) -> dict:
    snapshots = []
    records = []
    rendered = []
    for family in families:
        source = FIXTURES / FAMILIES[family]
        data = source.read_bytes()
        queries = snapshot_queries(data, str(source.relative_to(ROOT)))
        snapshots.append({
            "family": family,
            "source": str(source.relative_to(ROOT)),
            "source_sha256": hashlib.sha256(data).hexdigest(),
            "queries": len(queries),
        })
        for label, query in queries:
            filename = f"{family}--{label}.smt2"
            rendered.append((filename, query))
            records.append({
                "family": family, "label": label, "file": filename,
                "query_sha256": hashlib.sha256(query).hexdigest(),
            })
    # Refuse an existing destination, including a symlink. Failure cleanup owns
    # only the directory created here, never a caller's previous campaign.
    out.mkdir(mode=0o700)
    try:
        for filename, query in rendered:
            (out / filename).write_bytes(query)
        manifest = {
            "format": "trust-cg-x86-body-query-export-v1",
            "proof_credit": False,
            "snapshots": snapshots,
            "queries": records,
        }
        (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    except BaseException:
        shutil.rmtree(out)
        raise
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="new output directory outside the repository")
    parser.add_argument("--family", choices=FAMILIES, action="append", help="export this family; default: all twelve")
    args = parser.parse_args()
    families = list(dict.fromkeys(args.family or FAMILIES))
    out = args.out.absolute()
    if out.resolve().is_relative_to(ROOT.resolve()):
        parser.error("--out must be outside the repository")
    try:
        manifest = export(out, families)
    except (OSError, UnicodeError, ValueError) as error:
        print(f"export_x86_body_queries: refused: {error}", file=sys.stderr)
        return 2
    print(f"exported {len(manifest['queries'])} canonical queries to {out}; no proof credit")
    for snapshot in manifest["snapshots"]:
        print(f"  {snapshot['family']}: {snapshot['queries']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
