#!/usr/bin/env python3
"""Pack one qualify-neon-ld1-st1-20260923.py run into an in-tree archive.

usage: archive-neon-ld1-st1-20260923.py RUN ARCHIVE ROOT

Copies results.json and the mutant tables; gzip-compresses (mtime 0) every
log, disassembly and symbol listing, every retained object (the repository
ignores `*.o`, so objects are stored as `*.o.gz`) and the C oracle; copies
the harness scripts and the tested source file from ROOT; then writes
inventory.json listing every file except README.md. Nothing is re-run and no
record is altered.
"""
from pathlib import Path
import gzip
import hashlib
import io
import json
import shutil
import sys

RUN, ARCHIVE, ROOT = (Path(arg).resolve() for arg in sys.argv[1:4])
HERE = Path(__file__).resolve().parent
ARCHIVE.mkdir(parents=True, exist_ok=True)


def write_gz(dest: Path, data: bytes) -> None:
    dest.parent.mkdir(parents=True, exist_ok=True)
    buffer = io.BytesIO()
    with gzip.GzipFile(filename="", mode="wb", fileobj=buffer, mtime=0, compresslevel=9) as handle:
        handle.write(data)
    dest.with_name(dest.name + ".gz").write_bytes(buffer.getvalue())


records = ARCHIVE / "records"
records.mkdir(parents=True, exist_ok=True)
shutil.copyfile(RUN / "results.json", records / "results.json")
for log in sorted((RUN / "logs").iterdir()):
    write_gz(records / "logs" / log.name, log.read_bytes())
for path in sorted((RUN / "objects").iterdir()):
    if path.suffix == ".tsv":
        (records / "mutation").mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, records / "mutation" / path.name)
    elif path.suffix == ".c":
        write_gz(records / "oracle" / path.name, path.read_bytes())
    elif path.suffix == ".o":
        write_gz(records / "objects" / path.name, path.read_bytes())
    else:
        sys.exit(f"unexpected record {path.name}")
for folder in ("disasm", "symbols"):
    for path in sorted((RUN / folder).iterdir()):
        write_gz(records / folder / path.name, path.read_bytes())
for script in ("qualify-neon-ld1-st1-20260923.py", "archive-neon-ld1-st1-20260923.py"):
    dest = ARCHIVE / "harnesses" / script
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(HERE / script, dest)
relative = "crates/trust-cg-codegen/tests/neon_ld1_st1_post_execution.rs"
write_gz(ARCHIVE / "source" / Path(relative).name, (ROOT / relative).read_bytes())

artifacts = []
for path in sorted(p for p in ARCHIVE.rglob("*") if p.is_file()):
    name = path.relative_to(ARCHIVE).as_posix()
    if name in ("README.md", "inventory.json"):
        continue
    stored = path.read_bytes()
    entry = {"path": name}
    if path.name.endswith(".gz"):
        decoded = gzip.decompress(stored)
        entry.update(sha256=hashlib.sha256(decoded).hexdigest(), bytes=len(decoded),
                     stored_sha256=hashlib.sha256(stored).hexdigest(), stored_bytes=len(stored))
    else:
        entry.update(sha256=hashlib.sha256(stored).hexdigest(), bytes=len(stored))
    artifacts.append(entry)
(ARCHIVE / "inventory.json").write_text(json.dumps({"artifacts": artifacts}, indent=2) + "\n")
print(f"{len(artifacts)} artifacts inventoried")
