#!/usr/bin/env python3
"""Archive the staged L02-P10 qualifying run (merged head) into the repository.

Copies RUN/records into DEST/records, gzip-compressing logs, probe records,
objects, sources and trust-ir inputs (`*.gz`, recorded with decoded and
stored hashes), copies the harnesses, and writes DEST/inventory.json.
DEST/README.md is written by hand and is not listed (the archive checker
exempts it). Linked executables and shared objects are not archived; their
readelf and objdump records are.

Usage: archive-reloc-limits-staged-20260923.py RUN DEST
"""

from __future__ import annotations

import gzip
import hashlib
import json
import shutil
import sys
from pathlib import Path

RUN = Path(sys.argv[1]).resolve()
DEST = Path(sys.argv[2]).resolve()
PLAIN = {".json", ".py", ".patch"}
KEEP = {".log", ".txt", ".json", ".o", ".c", ".s", ".patch"}


def digest(data: bytes) -> tuple[str, int]:
    return hashlib.sha256(data).hexdigest(), len(data)


def store(source: Path, relative: str, artifacts: list[dict]) -> None:
    data = source.read_bytes()
    sha, size = digest(data)
    if source.suffix in PLAIN:
        target = DEST / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        artifacts.append({"path": relative, "sha256": sha, "bytes": size})
        return
    target = DEST / f"{relative}.gz"
    target.parent.mkdir(parents=True, exist_ok=True)
    # mtime=0 keeps the stored bytes reproducible.
    stored = gzip.compress(data, compresslevel=9, mtime=0)
    target.write_bytes(stored)
    stored_sha, stored_size = digest(stored)
    artifacts.append(
        {
            "path": f"{relative}.gz",
            "sha256": sha,
            "bytes": size,
            "stored_sha256": stored_sha,
            "stored_bytes": stored_size,
        }
    )


def main() -> int:
    for sub in ("records", "harnesses"):
        if (DEST / sub).exists():
            shutil.rmtree(DEST / sub)
    artifacts: list[dict] = []
    for source in sorted((RUN / "records").rglob("*")):
        if source.is_file() and source.suffix in KEEP:
            store(source, f"records/{source.relative_to(RUN / 'records').as_posix()}", artifacts)
    for source in sorted((RUN / "inputs").glob("*")):
        store(source, f"records/inputs/{source.name}", artifacts)
    for source in sorted((RUN / "harnesses").glob("*.py")):
        store(source, f"harnesses/{source.name}", artifacts)
    artifacts.sort(key=lambda entry: entry["path"])
    (DEST / "inventory.json").write_text(json.dumps({"artifacts": artifacts}, indent=2) + "\n")
    print(f"archived {len(artifacts)} artifacts into {DEST}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
