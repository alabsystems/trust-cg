#!/usr/bin/python3
"""Forward one tool call unchanged and record it for the C-01 BTI/PAC run.

Installed under the tool's own name (`cc`, `readelf` or `getconf`; argv[0]
selects it) in a directory placed first on PATH for the native test run only.
It checks the real executable's hash, runs it with the unchanged argument
vector and working directory, and records the request, stdout, stderr and
exit status. Files that the call names under the test scratch directories of
the two BTI/PAC tests (`*-force-bti-*`, `*-property-notes-*`) are snapshotted
by content before and after the call. It adds no authority and alters no file.
"""
from pathlib import Path
import hashlib, json, os, subprocess, sys, tempfile, time

root = Path(os.environ['C01_CAPTURE_ROOT'])
name = Path(sys.argv[0]).name
tools = json.loads((root / 'tools.json').read_text())
real = Path(tools[name]['path'])
assert hashlib.sha256(real.read_bytes()).hexdigest() == tools[name]['sha256']
folder = Path(tempfile.mkdtemp(prefix=name + '-', dir=root / 'calls'))
cwd = Path.cwd()
record = dict(tool=name, executable=str(real), sha256=tools[name]['sha256'],
              args=sys.argv[1:], cwd=str(cwd), started=time.time(), snapshots={})
SCRATCH = str((root / 'tmp').resolve()) + '/'
LABELS = ('-force-bti-', '-property-notes-')
LIMIT = 1024 * 1024


def snapshot(stage):
    candidates = set()
    for arg in sys.argv[1:]:
        if len(arg) < 4096:
            path = Path(arg)
            if not path.is_absolute():
                path = cwd / path
            resolved = str(path.resolve())
            if (path.is_file() and resolved.startswith(SCRATCH)
                    and any(label in resolved for label in LABELS)):
                candidates.add(path.resolve())
    rows = []
    for path in sorted(candidates):
        size = path.stat().st_size
        if size > LIMIT:
            rows.append(dict(path=str(path), bytes=size, skipped='larger than 1 MiB'))
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
