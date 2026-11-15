#!/usr/bin/env python3
"""Pack one qualify-bti-pac-2-20260923.py run directory into an in-tree archive.

usage: archive-bti-pac-2-20260923.py RUN ARCHIVE ROOT [MUTATION_LOG]

MUTATION_LOG, when given, is the development-time log of the broad-matcher
mutation run; it is stored gzip-compressed under records/mutation/.

Copies the run's results and tool identities, gzip-compresses (mtime 0) every
log, the direct listings and the one CG object the listings were taken from
(the repository ignores `*.o`), packs every recorded tool call and file snapshot into two deterministic
tarballs, copies the harness scripts and the exact sources under test from
ROOT, then writes inventory.json listing every file except README.md. Nothing
is re-run and no record is altered.
"""
from pathlib import Path
import gzip, hashlib, io, json, shutil, sys, tarfile

RUN, ARCHIVE, ROOT = (Path(arg).resolve() for arg in sys.argv[1:4])
MUTATION = Path(sys.argv[4]).resolve() if len(sys.argv) > 4 else None
HERE = Path(__file__).resolve().parent
ARCHIVE.mkdir(parents=True, exist_ok=True)


def write_gz(dest: Path, data: bytes):
    dest.parent.mkdir(parents=True, exist_ok=True)
    buffer = io.BytesIO()
    with gzip.GzipFile(filename='', mode='wb', fileobj=buffer, mtime=0, compresslevel=9) as handle:
        handle.write(data)
    dest.with_name(dest.name + '.gz').write_bytes(buffer.getvalue())


def tar_gz(dest: Path, source: Path):
    raw = io.BytesIO()
    with tarfile.open(fileobj=raw, mode='w', format=tarfile.PAX_FORMAT) as tar:
        for path in sorted(source.rglob('*')):
            info = tar.gettarinfo(str(path), arcname=str(path.relative_to(source.parent)))
            info.mtime, info.uid, info.gid, info.uname, info.gname = 0, 0, 0, '', ''
            if path.is_file():
                with path.open('rb') as handle:
                    tar.addfile(info, handle)
            else:
                tar.addfile(info)
    write_gz(dest, raw.getvalue())


records = ARCHIVE / 'records'
records.mkdir(parents=True, exist_ok=True)
shutil.copyfile(RUN / 'results.json', records / 'results.json')
shutil.copyfile(RUN / 'tools.json', records / 'tools.json')
for log in sorted((RUN / 'logs').iterdir()):
    write_gz(records / 'logs' / log.name, log.read_bytes())
# The CG object is stored gzip-compressed too: the repository ignores `*.o`.
for listing in sorted((RUN / 'direct').iterdir()):
    write_gz(records / 'direct' / listing.name, listing.read_bytes())
if MUTATION:
    write_gz(records / 'mutation' / 'broad-force-bti-matcher.log', MUTATION.read_bytes())
tar_gz(records / 'calls.tar', RUN / 'calls')
tar_gz(records / 'blobs.tar', RUN / 'blobs')

for script in ('qualify-bti-pac-2-20260923.py', 'capture-bti-pac-2-tools-20260923.py',
               'archive-bti-pac-2-20260923.py'):
    dest = ARCHIVE / 'harnesses' / script
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(HERE / script, dest)
for relative in ('crates/trust-cg-codegen/src/link_driver.rs',
                 'crates/trust-cg-codegen/tests/e2e_aarch64_elf_stack_zero_fill.rs'):
    write_gz(ARCHIVE / 'source' / Path(relative).name, (ROOT / relative).read_bytes())

artifacts = []
for path in sorted(p for p in ARCHIVE.rglob('*') if p.is_file()):
    relative = path.relative_to(ARCHIVE).as_posix()
    if relative in ('README.md', 'inventory.json'):
        continue
    stored = path.read_bytes()
    entry = dict(path=relative)
    if path.name.endswith('.gz') and not path.name.endswith('.tar.gz'):
        decoded = gzip.decompress(stored)
        entry.update(sha256=hashlib.sha256(decoded).hexdigest(), bytes=len(decoded),
                     stored_sha256=hashlib.sha256(stored).hexdigest(), stored_bytes=len(stored))
    elif path.name.endswith('.tar.gz'):
        decoded = gzip.decompress(stored)
        entry.update(sha256=hashlib.sha256(decoded).hexdigest(), bytes=len(decoded),
                     stored_sha256=hashlib.sha256(stored).hexdigest(), stored_bytes=len(stored))
    else:
        entry.update(sha256=hashlib.sha256(stored).hexdigest(), bytes=len(stored))
    artifacts.append(entry)
(ARCHIVE / 'inventory.json').write_text(json.dumps(dict(artifacts=artifacts), indent=2) + '\n')
print(f'{len(artifacts)} artifacts inventoried')
