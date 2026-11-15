#!/usr/bin/env python3
"""Archive the second L02-P9 repair run into the existing output-guard archive.

Copies RUN/records into DEST/records/repair-2, gzip-compressing logs and probe
records (`*.gz`, recorded with decoded and stored hashes; JSON and patches stay
plain), leaves out the probe working directory records/direct/cg (linked
binaries and input copies; its states and readelf/objdump records are kept),
adds this run's harnesses to DEST/harnesses, and regenerates DEST/inventory.json
over every file in the archive in the format the first run used. Entries for
files that were already archived must come out unchanged. DEST/README.md is
written by hand and is not listed (the archive checker exempts it).

Usage: archive-tls-output-guard-2-20260923.py RUN DEST
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
KEEP = {".log", ".txt", ".json", ".patch"}
HARNESSES = (
    "qualify-tls-output-guard-2-20260923.py",
    "mutation-tls-output-guard-2-20260923.py",
    "archive-tls-output-guard-2-20260923.py",
    "ld-option-reading-20260923.py",
    "ld-output-prefix-reading-20260923.py",
)


def digest(data: bytes) -> tuple[str, int]:
    return hashlib.sha256(data).hexdigest(), len(data)


def store(source: Path, relative: str) -> None:
    data = source.read_bytes()
    if source.suffix in PLAIN:
        target = DEST / relative
    else:
        target = DEST / f"{relative}.gz"
        # mtime=0 keeps the stored bytes reproducible.
        data = gzip.compress(data, compresslevel=9, mtime=0)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)


def entry(path: Path) -> dict:
    relative = path.relative_to(DEST).as_posix()
    data = path.read_bytes()
    if path.suffix == ".gz":
        sha, size = digest(gzip.decompress(data))
        stored_sha, stored_size = digest(data)
        return {"path": relative, "sha256": sha, "bytes": size, "stored_sha256": stored_sha, "stored_bytes": stored_size}
    sha, size = digest(data)
    return {"path": relative, "sha256": sha, "bytes": size}


def main() -> int:
    previous = {item["path"]: item for item in json.loads((DEST / "inventory.json").read_text())["artifacts"]}
    repair = DEST / "records" / "repair-2"
    if repair.exists():
        shutil.rmtree(repair)
    records = RUN / "records"
    for source in sorted(records.rglob("*")):
        relative = source.relative_to(records)
        if relative.parts[:2] == ("direct", "cg"):
            continue
        if source.is_file() and source.suffix in KEEP:
            store(source, f"records/repair-2/{relative.as_posix()}")
    for name in HARNESSES:
        store(RUN / name, f"harnesses/{name}")
    artifacts = [
        entry(path)
        for path in sorted(DEST.rglob("*"))
        if path.is_file() and path.relative_to(DEST).as_posix() not in ("README.md", "inventory.json")
    ]
    artifacts.sort(key=lambda item: item["path"])
    current = {item["path"]: item for item in artifacts}
    changed = [path for path, item in previous.items() if current.get(path) != item]
    if changed:
        print("previously archived entries changed:", changed, file=sys.stderr)
        return 1
    (DEST / "inventory.json").write_text(json.dumps({"artifacts": artifacts}, indent=2) + "\n")
    print(f"inventory lists {len(artifacts)} artifacts ({len(artifacts) - len(previous)} new) in {DEST}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
