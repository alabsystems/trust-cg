#!/usr/bin/python3
"""Forward exact tool arguments and retain independent debugger/CFI evidence."""
from pathlib import Path
import hashlib, json, os, shutil, subprocess, sys, tempfile, time

root = Path(os.environ['CG_CFI_CAPTURE_ROOT'])
name = Path(sys.argv[0]).name
tools = json.loads((root / 'tools.json').read_text())
real = Path(tools[name]['path'])
assert hashlib.sha256(real.read_bytes()).hexdigest() == tools[name]['sha256']
folder = Path(tempfile.mkdtemp(prefix=name + '-', dir=root / 'calls'))
cwd = Path.cwd()
record = dict(tool=name, executable=str(real), sha256=tools[name]['sha256'],
              args=sys.argv[1:], cwd=str(cwd), started=time.time(), snapshots={})

def snapshot(stage):
    candidates = set()
    for arg in sys.argv[1:]:
        if len(arg) < 4096:
            path = Path(arg)
            if path.is_file():
                candidates.add(path.resolve())
    if str(cwd).startswith('/tmp/trust_cg_elf_debugger_'):
        candidates.update(path.resolve() for path in cwd.iterdir() if path.is_file())
    rows = []
    for path in sorted(candidates):
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
