#!/usr/bin/env python3
"""Archive the 2026-09-23 L02-P7 COMDAT/explicit zero-fill qualifying run.

Copies from the run directory (--run, written by
qualify-comdat-explicit-zero-fill-20260923.py) and the mutation directory
(--mutation, written by mutation-comdat-explicit-zero-fill-20260923.py) and
the linker control (--control, written by lld-relro-control-20260923.py) into
--archive: results.json, every log gzip-compressed, and from each retained
native evidence directory its text files, C driver, link maps
(gzip-compressed) and emitted relocatable objects gzip-compressed as
`*.o.gz` (the root .gitignore ignores `*.o`, so a raw object would silently
stay out of the commit). Linked executables are recorded by SHA-256 and
length in records/native/linked-binaries.json, not copied. Writes
inventory.json last.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import shutil
from pathlib import Path

# (retained-directory prefix in the run's TMPDIR, archive subdirectory,
# expected directory count; several directories are one per level O0..O3)
NATIVE = [
    ("trust-cg-elf-stack-zero-link-once-native-", "link-once", 1),
    ("tcg-elf-sections-linux-explicit-nobits-", "explicit", 4),
    ("tcg-elf-sections-linux-ctor-nobits-", "ctor-bss-tcg", 4),
]
KEEP_SUFFIXES = {".txt", ".c"}
GZIP_SUFFIXES = {".o", ".map"}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def gzip_copy(source: Path, target: Path) -> None:
    with open(source, "rb") as handle, gzip.GzipFile(target, "wb", mtime=0) as stored:
        stored.write(handle.read())


def stamp(directory: Path) -> int:
    # `<prefix><pid>-<nanos>` (sections) or `<prefix><pid>-<nanos>-<seq>`.
    parts = directory.name[len(next(p for p, _, _ in NATIVE if directory.name.startswith(p))):]
    return int(parts.split("-")[1])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--mutation", type=Path, required=True)
    parser.add_argument("--control", type=Path, required=True)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--harness", type=Path, action="append", default=[])
    args = parser.parse_args()
    run, archive = args.run.resolve(), args.archive.resolve()
    records = archive / "records"
    (records / "logs").mkdir(parents=True, exist_ok=False)
    shutil.copy2(run / "results.json", records / "results.json")
    for log in sorted((run / "logs").glob("*.log")):
        gzip_copy(log, records / "logs" / f"{log.name}.gz")

    linked = {}
    for prefix, name, count in NATIVE:
        directories = sorted(
            (d for d in (run / "tmp").iterdir() if d.name.startswith(prefix)), key=stamp
        )
        assert len(directories) == count, (prefix, directories)
        for level, directory in enumerate(directories):
            target = records / "native" / name
            if count > 1:
                target = target / f"O{level}"
            target.mkdir(parents=True)
            (target / "CAPTURED_FROM.txt").write_text(f"{directory}\n")
            for item in sorted(directory.iterdir()):
                relative = f"{target.relative_to(records / 'native').as_posix()}/{item.name}"
                if item.suffix in GZIP_SUFFIXES:
                    gzip_copy(item, target / f"{item.name}.gz")
                elif item.suffix in KEEP_SUFFIXES:
                    shutil.copy2(item, target / item.name)
                elif item.suffix == "" and item.stat().st_mode & 0o111:
                    data = item.read_bytes()
                    linked[relative] = {"sha256": sha256_bytes(data), "bytes": len(data)}
                else:
                    raise SystemExit(f"unclassified evidence file {item}")
    (records / "native" / "linked-binaries.json").write_text(
        json.dumps(linked, indent=2, sort_keys=True) + "\n"
    )

    mutation = args.mutation.resolve()
    (records / "mutation").mkdir()
    shutil.copy2(mutation / "results.json", records / "mutation" / "results.json")
    for item in sorted(mutation.iterdir()):
        if item.suffix == ".log":
            gzip_copy(item, records / "mutation" / f"{item.name}.gz")
        elif item.suffix == ".diff":
            shutil.copy2(item, records / "mutation" / item.name)

    control = args.control.resolve()
    (records / "lld-relro-control").mkdir()
    for item in sorted(control.iterdir()):
        if item.suffix not in {".json", ".txt"}:
            raise SystemExit(f"unclassified control file {item}")
        shutil.copy2(item, records / "lld-relro-control" / item.name)

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
