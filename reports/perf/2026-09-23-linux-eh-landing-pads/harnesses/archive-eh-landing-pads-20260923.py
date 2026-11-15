#!/usr/bin/env python3
"""Retain the L03-P2 qualifying run as a durable archive (2026-09-23).

Copies the captured records into the archive directory, gzip-compresses
every log and JSON record (members are written with mtime 0 so the stored
bytes are reproducible), and writes inventory.json with the decoded and
stored SHA-256 and byte length of each gzip member.

    archive-eh-landing-pads-20260923.py <capture-root> <archive-dir>

<capture-root> holds floor/ (the Linux floor output directory), lib/,
eh-linux/, prefix/ and bridge/ (the bridge lane output directory; its
backend library snapshot is skipped and identified by hash only). README.md
and this harness are written by hand and listed as plain files.
"""

from __future__ import annotations

import gzip
import hashlib
import json
from pathlib import Path
import shutil
import sys

GROUPS = ("floor", "lib", "eh-linux", "prefix", "bridge")


def digest(data: bytes) -> tuple[str, int]:
    return hashlib.sha256(data).hexdigest(), len(data)


def main() -> int:
    capture, archive = (Path(arg) for arg in sys.argv[1:3])
    records = archive / "records"
    if records.exists():
        shutil.rmtree(records)
    for group in GROUPS:
        source = capture / group
        if not source.is_dir():
            continue
        for path in sorted(p for p in source.rglob("*") if p.is_file()):
            relative = path.relative_to(source)
            if path.suffix == ".so":
                # The bridge backend snapshot is identified by the report's
                # SHA-256, never copied into the tree.
                continue
            destination = records / group / relative.parent / f"{relative.name}.gz"
            destination.parent.mkdir(parents=True, exist_ok=True)
            with open(destination, "wb") as raw:
                with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as member:
                    member.write(path.read_bytes())
    artifacts = []
    for path in sorted(p for p in archive.rglob("*") if p.is_file()):
        relative = path.relative_to(archive).as_posix()
        if relative == "inventory.json":
            continue
        stored = path.read_bytes()
        entry = {"path": relative}
        if relative.endswith(".gz"):
            entry["sha256"], entry["bytes"] = digest(gzip.decompress(stored))
            entry["stored_sha256"], entry["stored_bytes"] = digest(stored)
        else:
            entry["sha256"], entry["bytes"] = digest(stored)
        artifacts.append(entry)
    inventory = {
        "schema": "trust-cg-evidence-inventory-v1",
        "description": (
            "L03-P2 qualifying run on Linux AArch64 (2026-09-23): the Linux floor with "
            "e2e_aarch64_eh_linux, library suites, the target's serial transcript, the "
            "pre-fix Resume control and the rustc bridge lane; gzip entries record decoded "
            "and stored hashes."
        ),
        "artifacts": artifacts,
    }
    (archive / "inventory.json").write_text(json.dumps(inventory, indent=2) + "\n")
    print(f"archived {len(artifacts)} files")
    return 0


if __name__ == "__main__":
    sys.exit(main())
