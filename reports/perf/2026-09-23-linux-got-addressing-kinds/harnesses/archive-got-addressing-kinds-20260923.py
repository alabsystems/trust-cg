#!/usr/bin/env python3
"""Archive a qualifying run of qualify-got-addressing-kinds-20260923.py in-tree.

Copies RUN/records into ARCHIVE/records with every file gzip-compressed
(deterministic: mtime 0) except results.json, copies the harnesses, and
writes ARCHIVE/inventory.json with each file's decoded SHA-256 and length
and, for a .gz file, the stored SHA-256 and length. RUN/work (the scratch
directory of the direct probes) is not archived; the small inputs and objects
the probes used were copied to RUN/records/inputs by the harness. README.md
is written by hand.

Usage: archive-got-addressing-kinds-20260923.py RUN ARCHIVE HARNESS...
"""

from __future__ import annotations

import gzip
import hashlib
import json
import shutil
import sys
from pathlib import Path

RUN = Path(sys.argv[1]).resolve()
ARCHIVE = Path(sys.argv[2]).resolve()
HARNESSES = [Path(p).resolve() for p in sys.argv[3:]]


def digest(data: bytes) -> tuple[str, int]:
    return hashlib.sha256(data).hexdigest(), len(data)


def main() -> int:
    records = ARCHIVE / "records"
    if records.exists():
        shutil.rmtree(records)
    artifacts = []
    for source in sorted((RUN / "records").rglob("*")):
        if not source.is_file():
            continue
        relative = source.relative_to(RUN)
        data = source.read_bytes()
        sha, size = digest(data)
        if source.name == "results.json":
            target = ARCHIVE / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            artifacts.append({"path": relative.as_posix(), "sha256": sha, "bytes": size})
            continue
        target = ARCHIVE / relative.with_name(relative.name + ".gz")
        target.parent.mkdir(parents=True, exist_ok=True)
        stored = gzip.compress(data, compresslevel=9, mtime=0)
        target.write_bytes(stored)
        stored_sha, stored_size = digest(stored)
        artifacts.append(
            {
                "path": target.relative_to(ARCHIVE).as_posix(),
                "sha256": sha,
                "bytes": size,
                "stored_sha256": stored_sha,
                "stored_bytes": stored_size,
            }
        )
    (ARCHIVE / "harnesses").mkdir(parents=True, exist_ok=True)
    for harness in HARNESSES:
        target = ARCHIVE / "harnesses" / harness.name
        shutil.copy(harness, target)
        sha, size = digest(target.read_bytes())
        artifacts.append({"path": f"harnesses/{harness.name}", "sha256": sha, "bytes": size})
    artifacts.sort(key=lambda entry: entry["path"])
    (ARCHIVE / "inventory.json").write_text(json.dumps({"artifacts": artifacts}, indent=2) + "\n")
    print(f"archived {len(artifacts)} artifacts under {ARCHIVE}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
