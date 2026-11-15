#!/usr/bin/env python3
"""Write inventory.json for this archive: every regular file except the
inventory itself, with SHA-256 and length; a `.gz` entry records the decoded
digest as `sha256`/`bytes` and the stored file as `stored_sha256`/`stored_bytes`
(the scripts/check_evidence_archive.py convention).

Usage: make-inventory-20260924.py <archive-dir>
"""

from __future__ import annotations

import gzip
import hashlib
import json
import sys
from pathlib import Path

ARCHIVE = Path(sys.argv[1]).resolve()
DESCRIPTION = (
    "L04-P11 second review repair on Linux AArch64 (2026-09-24): the Linux floor at "
    "02b3f18d7 (the ORR (vector) copy form and 16B OR binding, the TPREL adds as deferred "
    "rows) with the failed first attempt's report, the harness at 02b3f18d7 "
    "(verify/codegen/CLI targets, the native switch and indirect-call targets, ten "
    "mutation controls), the library re-run after the walk-query golden fix at "
    "fa9144ea1, and the value forms' SMT-LIB queries; gzip entries record decoded and "
    "stored hashes."
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
