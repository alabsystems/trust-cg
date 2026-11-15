#!/usr/bin/python3
"""Forward exact tool arguments and retain independent DWARF/debugger evidence.

Installed under the tool's own name (argv[0] selects it) in a directory placed
first on PATH and in TRUST_CG_LLVM_BIN. It checks the real executable's hash,
runs it with the unchanged argument vector and working directory, and records
the request, stdout, stderr, exit status and content snapshots of the test
scratch files it read or wrote (files under /tmp/trust_cg_*; objects,
executables, sources). It adds no authority and does not alter any file.
"""
from pathlib import Path
import hashlib, json, os, subprocess, sys, tempfile, time

root = Path(os.environ['CG_MODULE_DWARF_CAPTURE_ROOT'])
name = Path(sys.argv[0]).name
tools = json.loads((root / 'tools.json').read_text())
real = Path(tools[name]['path'])
assert hashlib.sha256(real.read_bytes()).hexdigest() == tools[name]['sha256']
folder = Path(tempfile.mkdtemp(prefix=name + '-', dir=root / 'calls'))
cwd = Path.cwd()
record = dict(tool=name, executable=str(real), sha256=tools[name]['sha256'],
              args=sys.argv[1:], cwd=str(cwd), started=time.time(), snapshots={})
SCRATCH = '/tmp/trust_cg_'
LIMIT = 32 * 1024 * 1024


def snapshot(stage):
    candidates = set()
    for arg in sys.argv[1:]:
        if len(arg) < 4096:
            path = Path(arg)
            if not path.is_absolute():
                path = cwd / path
            if path.is_file() and str(path.resolve()).startswith(SCRATCH):
                candidates.add(path.resolve())
    if str(cwd).startswith(SCRATCH):
        candidates.update(p.resolve() for p in cwd.iterdir() if p.is_file())
    rows = []
    for path in sorted(candidates):
        size = path.stat().st_size
        if size > LIMIT:
            rows.append(dict(path=str(path), bytes=size, skipped='larger than 32 MiB'))
            continue
        raw = path.read_bytes()
        sha = hashlib.sha256(raw).hexdigest()
        dest = root / 'blobs' / sha
        if not dest.exists():
            dest.write_bytes(raw)
        rows.append(dict(path=str(path), sha256=sha, bytes=len(raw), mode=path.stat().st_mode))
    record['snapshots'][stage] = rows


snapshot('before')
(folder / 'request.json').write_text(json.dumps(record, indent=2) + '\n')
result = subprocess.run([str(real), *sys.argv[1:]], capture_output=True)
(folder / 'stdout').write_bytes(result.stdout)
(folder / 'stderr').write_bytes(result.stderr)
snapshot('after')
record.update(exit_code=result.returncode, finished=time.time())
assert hashlib.sha256(real.read_bytes()).hexdigest() == record['sha256']
(folder / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
sys.stdout.buffer.write(result.stdout)
sys.stderr.buffer.write(result.stderr)
raise SystemExit(result.returncode if result.returncode >= 0 else 128 - result.returncode)
