#!/usr/bin/env python3
"""Archive the 2026-09-23 ELF function visibility/sections qualifying run.

Copies from the run directory (--run, written by
qualify-elf-function-attrs-20260923.py) into --archive: results.json, every
log gzip-compressed, and from each native evidence directory its text files,
C sources, trust-ir text and emitted relocatable objects. Linked shared
objects and executables are recorded by SHA-256 and length in
records/native/linked-binaries.json, not copied. Writes inventory.json last.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import shutil
from pathlib import Path

# (retained-name prefix in the run's TMPDIR, archive subdirectory)
NATIVE = [
    ("tcg-elf-binding-visibility-v45-", "visibility-v45"),
    ("tcg-elf-sections-linux-named-gc-", "named-gc"),
]
KEEP_SUFFIXES = {".txt", ".c", ".tir", ".o"}
LINKED = {"libtcgv45.so", "libinterpose.so", "driver", "gc", "nogc"}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--harness", type=Path, action="append", default=[])
    args = parser.parse_args()
    run, archive = args.run.resolve(), args.archive.resolve()
    records = archive / "records"
    (records / "logs").mkdir(parents=True, exist_ok=False)
    shutil.copy2(run / "results.json", records / "results.json")
    for log in sorted((run / "logs").glob("*.log")):
        with open(log, "rb") as source, gzip.GzipFile(
            records / "logs" / f"{log.name}.gz", "wb", mtime=0
        ) as target:
            target.write(source.read())
    linked = {}
    for prefix, name in NATIVE:
        # Each test loops O0..O3 and names its directory by a nanosecond
        # stamp, so ascending stamp order is optimization-level order.
        directories = sorted(
            (d for d in (run / "tmp").iterdir() if d.name.startswith(prefix)),
            key=lambda d: int(d.name.rsplit("-", 1)[1]),
        )
        assert len(directories) == 4, (prefix, directories)
        for level, directory in enumerate(directories):
            target = records / "native" / name / f"O{level}"
            target.mkdir(parents=True)
            (target / "CAPTURED_FROM.txt").write_text(f"{directory}\n")
            for item in sorted(directory.iterdir()):
                if item.name in LINKED:
                    data = item.read_bytes()
                    linked[f"{name}/O{level}/{item.name}"] = {
                        "sha256": sha256_bytes(data),
                        "bytes": len(data),
                    }
                elif item.suffix in KEEP_SUFFIXES:
                    shutil.copy2(item, target / item.name)
    (records / "native" / "linked-binaries.json").write_text(
        json.dumps(linked, indent=2, sort_keys=True) + "\n"
    )
    (archive / "harnesses").mkdir()
    for harness in args.harness:
        shutil.copy2(harness, archive / "harnesses" / harness.name)

    artifacts = []
    for path in sorted(p for p in archive.rglob("*") if p.is_file()):
        relative = path.relative_to(archive).as_posix()
        if relative in {"inventory.json", "README.md"}:
            continue
        stored = path.read_bytes()
        entry = {"path": relative}
        if path.suffix == ".gz":
            decoded = gzip.decompress(stored)
            entry |= {
                "sha256": sha256_bytes(decoded),
                "bytes": len(decoded),
                "stored_sha256": sha256_bytes(stored),
                "stored_bytes": len(stored),
            }
        else:
            entry |= {"sha256": sha256_bytes(stored), "bytes": len(stored)}
        artifacts.append(entry)
    (archive / "inventory.json").write_text(json.dumps({"artifacts": artifacts}, indent=2) + "\n")
    print(f"archived {len(artifacts)} files into {archive}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
