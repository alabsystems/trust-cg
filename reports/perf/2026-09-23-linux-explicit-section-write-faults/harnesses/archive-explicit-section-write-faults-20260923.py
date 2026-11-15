#!/usr/bin/env python3
"""Archive the 2026-09-23 L02-P3 explicit-section placement run.

Copies into --archive:

* from the qualifying run (--run, written by
  qualify-explicit-section-write-faults-20260923.py): results.json, every
  log gzip-compressed, and from the retained native directories of
  e2e_aarch64_elf_sections the refused-name controls (records/native/refused,
  one directory per case) and the honoured-name rows (records/native/honoured);
* from the linker probe (--probe, written by linker-placement-probe-20260923.py):
  results.json (gzip-compressed), summary.txt and the `ld --verbose` scripts;
* from each mutation batch (--mutation, written by
  mutation-explicit-section-write-faults-20260923.py): the merged
  results.json, each diff, each log gzip-compressed, and from every refused
  control whose name escaped its refusal under the mutation the escaped
  object, its link diagnostics and run records.

Relocatable objects are stored as `*.o.gz` (the root .gitignore ignores
`*.o`). Linked executables and shared libraries are recorded by SHA-256 and
length in linked-binaries.json, not copied. Writes inventory.json last.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import re
import shutil
from pathlib import Path

KEEP_SUFFIXES = {".txt", ".c", ".json", ".x"}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def gzip_copy(source: Path, target: Path) -> None:
    with open(source, "rb") as handle, gzip.GzipFile(target, "wb", mtime=0) as stored:
        stored.write(handle.read())


def case_label(directory: Path) -> str:
    record = (directory / "record.txt").read_text()
    name = re.search(r"^name (\S+)$", record, re.MULTILINE)[1]
    comdat = re.search(r"^comdat symbol Some\(\"([^\"]+)\"\)$", record, re.MULTILINE)
    index = int(directory.name.split("-")[5])
    label = re.sub(r"[^A-Za-z0-9]+", "_", name).strip("_")
    if comdat:
        label = f"comdat_{label}"
    return f"{index:02d}-{label}"


def copy_evidence(source: Path, target: Path, linked: dict, root: Path,
                  only=lambda item: True) -> None:
    target.mkdir(parents=True)
    (target / "CAPTURED_FROM.txt").write_text(f"{source}\n")
    for item in sorted(source.iterdir()):
        if not only(item):
            continue
        relative = f"{target.relative_to(root).as_posix()}/{item.name}"
        if item.suffix == ".o":
            gzip_copy(item, target / f"{item.name}.gz")
        elif item.suffix in KEEP_SUFFIXES:
            shutil.copy2(item, target / item.name)
        elif item.suffix in {".exe", ".so"} or (item.suffix == "" and item.stat().st_mode & 0o111):
            data = item.read_bytes()
            linked[relative] = {"sha256": sha256_bytes(data), "bytes": len(data)}
        else:
            raise SystemExit(f"unclassified evidence file {item}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--probe", type=Path, required=True)
    parser.add_argument("--mutation", type=Path, action="append", default=[])
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--harness", type=Path, action="append", default=[])
    args = parser.parse_args()
    run, archive = args.run.resolve(), args.archive.resolve()
    records = archive / "records"
    (records / "logs").mkdir(parents=True, exist_ok=False)
    shutil.copy2(run / "results.json", records / "results.json")
    for log in sorted((run / "logs").glob("*.log")):
        gzip_copy(log, records / "logs" / f"{log.name}.gz")

    native = records / "native"
    linked: dict = {}
    refused = sorted((d for d in (run / "tmp").iterdir()
                      if d.name.startswith("tcg-elf-sections-linux-refused-")),
                     key=lambda d: int(d.name.split("-")[5]))
    assert len(refused) >= 29, [d.name for d in refused]
    for directory in refused:
        copy_evidence(directory, native / "refused" / case_label(directory), linked, native)
    honoured = sorted(d for d in (run / "tmp").iterdir()
                      if d.name.startswith("tcg-elf-sections-linux-honoured-"))
    assert len(honoured) == 2, honoured
    for directory in honoured:
        level = directory.name.split("-")[5]
        copy_evidence(directory, native / "honoured" / level, linked, native)
    (native / "linked-binaries.json").write_text(json.dumps(linked, indent=2, sort_keys=True) + "\n")

    probe = args.probe.resolve()
    (records / "probe" / "scripts").mkdir(parents=True)
    gzip_copy(probe / "results.json", records / "probe" / "results.json.gz")
    shutil.copy2(probe / "summary.txt", records / "probe" / "summary.txt")
    for script in sorted((probe / "scripts").iterdir()):
        shutil.copy2(script, records / "probe" / "scripts" / script.name)

    mutation_root = records / "mutation"
    mutation_root.mkdir()
    batches, escaped_linked = [], {}
    for batch in args.mutation:
        batch = batch.resolve()
        batches.append(json.loads((batch / "results.json").read_text()))
        for item in sorted(batch.iterdir()):
            if item.suffix == ".diff":
                shutil.copy2(item, mutation_root / item.name)
            elif item.suffix == ".log":
                gzip_copy(item, mutation_root / f"{item.name}.gz")
            elif item.is_dir() and item.name.endswith("-tmp-e2e"):
                mutation = item.name[: -len("-tmp-e2e")]
                for directory in sorted(item.iterdir()):
                    record = directory / "record.txt"
                    if not (directory.name.startswith("tcg-elf-sections-linux-refused-")
                            and record.exists() and "was NOT refused" in record.read_text()):
                        continue
                    copy_evidence(
                        directory,
                        mutation_root / mutation / case_label(directory),
                        escaped_linked,
                        mutation_root,
                        only=lambda path: path.name.startswith(("escaped-", "libescaped-"))
                        or path.name in {"record.txt", "driver.c"},
                    )
    (mutation_root / "results.json").write_text(json.dumps({"batches": batches}, indent=2) + "\n")
    (mutation_root / "linked-binaries.json").write_text(
        json.dumps(escaped_linked, indent=2, sort_keys=True) + "\n")

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
