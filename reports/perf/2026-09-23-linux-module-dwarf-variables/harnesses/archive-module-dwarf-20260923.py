#!/usr/bin/env python3
"""Pack one qualify-module-dwarf-20260923.py output directory into an in-tree archive.

usage: archive-module-dwarf-20260923.py RUN ARCHIVE ROOT

Copies (gzip-compressed, mtime 0) the run's results, tool identities, logs and
every gdb call record; packs all captured calls and file snapshots into two
deterministic tarballs; copies the harness scripts and the exact test sources
from ROOT; then writes inventory.json listing every file except README.md.
Nothing is re-run and no record is altered.
"""
from pathlib import Path
import gzip, hashlib, io, json, shutil, sys, tarfile

RUN, ARCHIVE, ROOT = (Path(arg).resolve() for arg in sys.argv[1:4])
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
        for path in sorted(p for p in source.rglob('*')):
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
for call in sorted((RUN / 'calls').iterdir()):
    result = json.loads((call / 'result.json').read_text())
    if result['tool'] != 'gdb':
        continue
    for name in ('request.json', 'result.json'):
        dest = records / 'gdb' / call.name / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(call / name, dest)
    for name in ('stdout', 'stderr'):
        write_gz(records / 'gdb' / call.name / name, (call / name).read_bytes())
tar_gz(records / 'calls.tar', RUN / 'calls')
tar_gz(records / 'blobs.tar', RUN / 'blobs')

for script in ('qualify-module-dwarf-20260923.py', 'capture-module-dwarf-tools-20260923.py',
               'archive-module-dwarf-20260923.py'):
    dest = ARCHIVE / 'harnesses' / script
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(HERE / script, dest)
for relative in ('tests/aarch64_elf_dwarf.rs', 'tests/e2e_aarch64_elf_debugger_linux.rs',
                 'tests/common/elf_debug_fixture.rs', 'tests/common/llvm_tools.rs'):
    source = ROOT / 'crates/trust-cg-codegen' / relative
    write_gz(ARCHIVE / 'test-source' / relative.removeprefix('tests/'), source.read_bytes())

artifacts = []
for path in sorted(p for p in ARCHIVE.rglob('*') if p.is_file()):
    relative = path.relative_to(ARCHIVE).as_posix()
    if relative in ('README.md', 'inventory.json'):
        continue
    stored = path.read_bytes()
    entry = dict(path=relative)
    if path.name.endswith('.gz'):
        decoded = gzip.decompress(stored)
        entry.update(sha256=hashlib.sha256(decoded).hexdigest(), bytes=len(decoded),
                     stored_sha256=hashlib.sha256(stored).hexdigest(), stored_bytes=len(stored))
    else:
        entry.update(sha256=hashlib.sha256(stored).hexdigest(), bytes=len(stored))
    artifacts.append(entry)
(ARCHIVE / 'inventory.json').write_text(json.dumps(dict(artifacts=artifacts), indent=2) + '\n')
print(json.dumps(dict(artifacts=len(artifacts))))
