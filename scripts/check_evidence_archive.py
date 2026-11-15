#!/usr/bin/env python3
"""Verify an in-tree evidence archive against its hashed inventory.

``check_evidence_archive.py DIR [DIR ...]`` verifies in-tree archives. Each
directory needs a ``README.md`` and a top-level ``inventory.json`` or
``SHA256SUMS``. Nested inventories cover their own subtrees. Every other
regular file must be listed, every listed file must exist inside the archive
without symlinks, and its SHA-256 and byte length must match. An entry with
``stored_sha256``/``stored_bytes`` describes a gzip file: the stored bytes and
the decoded bytes must both match. A missing, unlisted, extra, symlinked or
mismatched file fails the archive, and so do two names that differ only in case
or Unicode normalization, which a case-insensitive filesystem stores as one.

A development record whose payload was removed from the tree fails this check
at HEAD by design; run it on the commit its README names as the last one that
contains the payload. The check does not run a test, establish that a
record's claim is true, or turn a host-local record into evidence. Exit
status: 0 when every archive passes, 1 on any failure, 2 when an input cannot
be read.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys
import zlib


README = "README.md"
INVENTORY = "inventory.json"
SUMS = "SHA256SUMS"
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
SUMS_LINE = re.compile(r"([0-9a-f]{64}) [ *](.+)\Z")
CHUNK = 1 << 20


def is_count(value) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def safe_relative(raw) -> PurePosixPath | None:
    if not isinstance(raw, str) or not raw or raw.startswith("/") or "\\" in raw:
        return None
    if any(part in ("", ".", "..") for part in raw.split("/")):
        return None
    return PurePosixPath(raw)


def digest(path: Path) -> tuple[str, int]:
    hasher, size = hashlib.sha256(), 0
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(CHUNK), b""):
            hasher.update(block)
            size += len(block)
    return hasher.hexdigest(), size


def decoded_digest(path: Path, limit: int) -> tuple[str, int] | None:
    """Hash gzip-decoded bytes, reading at most one byte beyond ``limit``."""
    hasher, size = hashlib.sha256(), 0
    try:
        with gzip.open(path, "rb") as handle:
            while size <= limit:
                block = handle.read(min(CHUNK, limit + 1 - size))
                if not block:
                    break
                hasher.update(block)
                size += len(block)
    except (OSError, EOFError, zlib.error):
        return None
    return hasher.hexdigest(), size


def archive_files(directory: Path) -> tuple[set[str], list[str]]:
    files, errors = set(), []
    for current, dirnames, filenames in os.walk(directory):
        base = Path(current)
        for name in sorted(dirnames):
            if (base / name).is_symlink():
                errors.append(f"{base / name}: symlinked directory in archive")
        dirnames[:] = [name for name in dirnames if not (base / name).is_symlink()]
        for name in filenames:
            path = base / name
            mode = path.lstat().st_mode
            relative = path.relative_to(directory).as_posix()
            if not stat.S_ISREG(mode):
                errors.append(f"{path}: archive member is not a regular file")
                continue
            files.add(relative)
    return files, errors


def inventory_entries(path: Path) -> tuple[list[dict], list[str]]:
    try:
        document = json.loads(path.read_text())
    except ValueError as error:
        return [], [f"{path}: invalid JSON: {error}"]
    entries = document.get("artifacts") if isinstance(document, dict) else document
    if not isinstance(entries, list) or not entries:
        return [], [f"{path}: expected a non-empty artifact list"]
    return entries, []


def entry_errors(inventory: Path, entry, prefix: PurePosixPath, listed: dict[str, str]) -> list[str]:
    if not isinstance(entry, dict):
        return [f"{inventory}: artifact entry is not an object"]
    relative = safe_relative(entry.get("path"))
    if relative is None:
        return [f"{inventory}: unsafe or missing artifact path {entry.get('path')!r}"]
    name = (prefix / relative).as_posix()
    if listed.get(name) == str(inventory):
        return [f"{inventory}: duplicate artifact {relative}"]
    listed[name] = str(inventory)
    if not HEX64.match(str(entry.get("sha256", ""))) or not is_count(entry.get("bytes")):
        return [f"{inventory}: {relative}: needs a 64-hex sha256 and a byte count"]
    stored = ("stored_sha256" in entry, "stored_bytes" in entry)
    if stored[0] != stored[1]:
        return [f"{inventory}: {relative}: stored_sha256 and stored_bytes must appear together"]
    target = inventory.parent / relative
    if not target.is_file() or target.is_symlink():
        return [f"{inventory}: {relative}: listed file is missing"]
    actual = digest(target)
    if not stored[0]:
        if actual != (entry["sha256"], entry["bytes"]):
            return [f"{inventory}: {relative}: SHA-256/length mismatch"]
        return []
    if not HEX64.match(str(entry["stored_sha256"])) or not is_count(entry["stored_bytes"]):
        return [f"{inventory}: {relative}: needs a 64-hex stored_sha256 and a stored byte count"]
    if actual != (entry["stored_sha256"], entry["stored_bytes"]):
        return [f"{inventory}: {relative}: stored SHA-256/length mismatch"]
    if not relative.name.endswith(".gz"):
        return [f"{inventory}: {relative}: stored hashes recorded for a file with no known encoding"]
    decoded = decoded_digest(target, entry["bytes"])
    if decoded is None:
        return [f"{inventory}: {relative}: gzip member cannot be decoded"]
    if decoded != (entry["sha256"], entry["bytes"]):
        return [f"{inventory}: {relative}: decoded SHA-256/length mismatch"]
    return []


def sums_errors(path: Path, prefix: PurePosixPath, listed: dict[str, str]) -> list[str]:
    errors, count = [], 0
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip():
            continue
        match = SUMS_LINE.match(line)
        relative = safe_relative(match[2]) if match else None
        if relative is None:
            errors.append(f"{path}:{number}: malformed SHA256SUMS line")
            continue
        count += 1
        name = (prefix / relative).as_posix()
        if listed.get(name) == str(path):
            errors.append(f"{path}:{number}: duplicate artifact {relative}")
            continue
        listed[name] = str(path)
        target = path.parent / relative
        if not target.is_file() or target.is_symlink():
            errors.append(f"{path}:{number}: listed file is missing: {relative}")
        elif digest(target)[0] != match[1]:
            errors.append(f"{path}:{number}: SHA-256 mismatch: {relative}")
    if count == 0:
        errors.append(f"{path}: lists no artifacts")
    return errors


def archive_errors(directory: Path) -> list[str]:
    """Return every durability failure for one archive directory."""
    if directory.is_symlink() or not directory.is_dir():
        return [f"{directory}: not an archive directory"]
    files, errors = archive_files(directory)
    if README not in files:
        errors.append(f"{directory}: missing {README} stating the claim and its boundary")
    inventories = sorted(name for name in files if PurePosixPath(name).name in (INVENTORY, SUMS))
    if not any("/" not in name for name in inventories):
        errors.append(f"{directory}: missing top-level {INVENTORY} or {SUMS}")
    listed: dict[str, str] = {}
    for name in inventories:
        path = directory / name
        prefix = PurePosixPath(name).parent
        if path.name == SUMS:
            errors.extend(sums_errors(path, prefix, listed))
            continue
        entries, problems = inventory_entries(path)
        errors.extend(problems)
        for entry in entries:
            errors.extend(entry_errors(path, entry, prefix, listed))
    for name in sorted(files - set(listed) - set(inventories) - {README}):
        errors.append(f"{directory}: {name} is not listed by any inventory, so it is not archived")
    # Names that differ only in case or Unicode normalization are one file on
    # a case-insensitive filesystem (macOS's default): a checkout keeps one of
    # them, so the archive cannot hold both records it lists.
    for names in case_collisions().collisions(files | set(listed)):
        errors.append(f"{directory}: {', '.join(names)} are one file on a case-insensitive filesystem")
    return errors


def case_collisions():
    """scripts/check_path_case_collisions.py, which owns the path fold."""
    spec = importlib.util.spec_from_file_location(
        "_evidence_check_path_case_collisions", Path(__file__).resolve().with_name("check_path_case_collisions.py")
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("archives", nargs="+", type=Path, help="archive directories to verify")
    args = parser.parse_args(argv)
    errors: list[str] = []
    try:
        for directory in args.archives:
            errors.extend(archive_errors(directory))
    except (OSError, UnicodeError) as error:
        print(f"evidence archive check failed: {error}", file=sys.stderr)
        return 2
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Evidence archive checks passed: {len(args.archives)} archive(s).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
