from pathlib import Path
import hashlib, json, subprocess

r = Path('/home/ayates/trust-cg-soundness-20260914')
c = Path('/home/ayates/trust-cg-output-source-capture-20260917')
record = json.loads((r / 'cg-call-frame-repaired-instrumentation.json').read_text())
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=c, text=True).strip() == record['source']
for name, sha in record['after'].items():
    assert hashlib.sha256((c / name).read_bytes()).hexdigest() == sha, name
subprocess.run(['git', 'restore', '--source=HEAD', '--staged', '--worktree', '--', *record['after']], cwd=c, check=True)
for name, sha in record['before'].items():
    assert hashlib.sha256((c / name).read_bytes()).hexdigest() == sha, name
assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=c)
(r / 'cg-call-frame-repaired-capture-restored.json').write_text(json.dumps(dict(source=record['source'], files=record['before'], clean=True), indent=2) + '\n')
print('Diagnostic capture instrumentation removed; checkout clean.')
