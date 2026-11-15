#!/usr/bin/env python3
"""Archive a qualifying run of qualify-got-base-repair-20260923.py into the
third L02-P10 closure audit's archive, under records/repair.

Copies RUN/records into ARCHIVE/records/repair with every file
gzip-compressed (deterministic: mtime 0) except results.json; the per-phase
files (phase-*.json) are left out because results.json holds each of them
verbatim. Copies the harnesses into ARCHIVE/harnesses, then rewrites
ARCHIVE/inventory.json over every file of the archive except README.md and
inventory.json, in the archive's format: each file's decoded SHA-256 and
length and, for a .gz file, the stored SHA-256 and length. The earlier
records are not touched. RUN/work (the probes' scratch directory) is not
archived; the small inputs the probes used are in RUN/records/inputs.
README.md is written by hand.

Usage: archive-got-base-repair-20260923.py RUN ARCHIVE HARNESS...
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
    repair = ARCHIVE / "records" / "repair"
    if repair.exists():
        shutil.rmtree(repair)
    for source in sorted((RUN / "records").rglob("*")):
        if not source.is_file() or (source.parent == RUN / "records" and source.name.startswith("phase-")):
            continue
        relative = source.relative_to(RUN / "records")
        data = source.read_bytes()
        if source.name == "results.json":
            target = repair / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            continue
        target = repair / relative.with_name(relative.name + ".gz")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(gzip.compress(data, compresslevel=9, mtime=0))
    (ARCHIVE / "harnesses").mkdir(parents=True, exist_ok=True)
    for harness in HARNESSES:
        shutil.copy(harness, ARCHIVE / "harnesses" / harness.name)
    artifacts = []
    for path in sorted(ARCHIVE.rglob("*")):
        if not path.is_file() or path.relative_to(ARCHIVE).as_posix() in ("README.md", "inventory.json"):
            continue
        stored = path.read_bytes()
        entry = {"path": path.relative_to(ARCHIVE).as_posix()}
        if path.suffix == ".gz":
            entry["sha256"], entry["bytes"] = digest(gzip.decompress(stored))
            entry["stored_sha256"], entry["stored_bytes"] = digest(stored)
        else:
            entry["sha256"], entry["bytes"] = digest(stored)
        artifacts.append(entry)
    artifacts.sort(key=lambda entry: entry["path"])
    (ARCHIVE / "inventory.json").write_text(json.dumps({"artifacts": artifacts}, indent=2) + "\n")
    print(f"archived {len(artifacts)} artifacts under {ARCHIVE}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
