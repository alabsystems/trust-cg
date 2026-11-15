#!/usr/bin/env python3
"""Add the L03-P2 evidence-repair records to the landing-pad archive (2026-09-23).

The original records (floor/, lib/, eh-linux/, prefix/, bridge/) are left
untouched. This copies each repair group from the capture root into
records/<group>/, gzip-compressing every file (members written with mtime 0
so the stored bytes are reproducible), then rewrites inventory.json over the
whole archive with the decoded and stored SHA-256 and byte length of each
gzip member.

    archive-eh-landing-pads-repair-20260923.py <capture-root> <archive-dir>

<capture-root> holds floor-fd1a09822/ (the Linux floor output directory and
its stdout), lib-fd1a09822/, eh-linux-fd1a09822/ and prefix-per-function/.
"""

from __future__ import annotations

import gzip
import hashlib
import json
from pathlib import Path
import shutil
import sys

GROUPS = ("floor-fd1a09822", "lib-fd1a09822", "eh-linux-fd1a09822", "prefix-per-function")


def digest(data: bytes) -> tuple[str, int]:
    return hashlib.sha256(data).hexdigest(), len(data)


def main() -> int:
    capture, archive = (Path(arg) for arg in sys.argv[1:3])
    records = archive / "records"
    for group in GROUPS:
        source = capture / group
        if not source.is_dir():
            raise SystemExit(f"missing capture group {source}")
        destination_root = records / group
        if destination_root.exists():
            shutil.rmtree(destination_root)
        for path in sorted(p for p in source.rglob("*") if p.is_file()):
            relative = path.relative_to(source)
            destination = destination_root / relative.parent / f"{relative.name}.gz"
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
            "pre-fix Resume control and the rustc bridge lane at 62234066b, plus the "
            "evidence repair at fd1a09822 (floor, library suites, transcript with "
            "separate mutant and reference counts, execve trace, per-function pre-fix "
            "probe); gzip entries record decoded and stored hashes."
        ),
        "artifacts": artifacts,
    }
    (archive / "inventory.json").write_text(json.dumps(inventory, indent=2) + "\n")
    print(f"archived {len(artifacts)} files")
    return 0


if __name__ == "__main__":
    sys.exit(main())
