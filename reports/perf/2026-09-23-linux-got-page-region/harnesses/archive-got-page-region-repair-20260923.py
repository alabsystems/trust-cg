#!/usr/bin/env python3
"""Archive the L02-P10 second-repair qualifying run into records/repair/ of an existing archive.

Copies RUN/records into DEST/records/repair, gzip-compressing logs, probe
records, objects, sources, linker scripts and trust-ir inputs (`*.gz`,
recorded with decoded and stored hashes), copies RUN/harnesses into
DEST/harnesses, and rewrites DEST/inventory.json: the entries of the first
run are kept as they are, and every entry under records/repair/ or naming
one of these harnesses is replaced. DEST/README.md is written by hand and
is not listed (the archive checker exempts it). Linked executables are not
archived; their readelf and objdump records are.

Usage: archive-got-page-region-repair-20260923.py RUN DEST
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
PREFIX = "records/repair"
PLAIN = {".json", ".py", ".patch"}
KEEP = {".log", ".txt", ".json", ".o", ".c", ".s", ".ld", ".patch"}


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
    inventory = DEST / "inventory.json"
    previous = json.loads(inventory.read_text())["artifacts"]
    harnesses = {f"harnesses/{source.name}" for source in (RUN / "harnesses").glob("*.py")}
    kept = [entry for entry in previous
            if not entry["path"].startswith(f"{PREFIX}/") and entry["path"] not in harnesses]
    if (DEST / PREFIX).exists():
        shutil.rmtree(DEST / PREFIX)
    artifacts: list[dict] = []
    for source in sorted((RUN / "records").rglob("*")):
        if source.is_file() and source.suffix in KEEP:
            store(source, f"{PREFIX}/{source.relative_to(RUN / 'records').as_posix()}", artifacts)
    for source in sorted((RUN / "inputs").glob("*")):
        store(source, f"{PREFIX}/inputs/{source.name}", artifacts)
    for source in sorted((RUN / "harnesses").glob("*.py")):
        store(source, f"harnesses/{source.name}", artifacts)
    merged = sorted(kept + artifacts, key=lambda entry: entry["path"])
    inventory.write_text(json.dumps({"artifacts": merged}, indent=2) + "\n")
    print(f"archived {len(artifacts)} artifacts into {DEST / PREFIX}; inventory lists {len(merged)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
