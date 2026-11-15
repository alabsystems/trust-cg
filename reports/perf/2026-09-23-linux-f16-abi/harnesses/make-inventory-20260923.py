#!/usr/bin/env python3
"""Write inventory.json for this archive: every regular file except the
inventory itself, with SHA-256 and length; a `.gz` entry records the decoded
digest as `sha256`/`bytes` and the stored file as `stored_sha256`/`stored_bytes`
(the scripts/check_evidence_archive.py convention).

Usage: make-inventory-20260923.py <archive-dir>
"""

from __future__ import annotations

import gzip
import hashlib
import json
import sys
from pathlib import Path

ARCHIVE = Path(sys.argv[1]).resolve()
DESCRIPTION = (
    "L01-P7 f16 scalar and f16 HFA calling-convention qualifying run on Linux "
    "AArch64 at 2ac464924 (2026-09-23): e2e_aarch64_f16_abi_linux with retained "
    "objects, the four existing f16 natives, the stock-rustc DarwinPCS/AAPCS64 "
    "HFA stack-placement probe and the InsertField shared-storage reproducer; "
    "gzip entries record decoded and stored hashes."
)


def digest(data: bytes) -> tuple[str, int]:
    return hashlib.sha256(data).hexdigest(), len(data)


def main() -> int:
    artifacts = []
    for path in sorted(p for p in ARCHIVE.rglob("*") if p.is_file()):
        relative = path.relative_to(ARCHIVE).as_posix()
        if relative == "inventory.json":
            continue
        stored = path.read_bytes()
        entry = {"path": relative}
        if path.suffix == ".gz":
            entry["sha256"], entry["bytes"] = digest(gzip.decompress(stored))
            entry["stored_sha256"], entry["stored_bytes"] = digest(stored)
        else:
            entry["sha256"], entry["bytes"] = digest(stored)
        artifacts.append(entry)
    document = {
        "schema": "trust-cg-evidence-inventory-v1",
        "description": DESCRIPTION,
        "artifacts": artifacts,
    }
    (ARCHIVE / "inventory.json").write_text(json.dumps(document, indent=2) + "\n")
    print(f"{len(artifacts)} artifacts")
    return 0


if __name__ == "__main__":
    sys.exit(main())
