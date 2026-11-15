from pathlib import Path
import hashlib, json, shutil, subprocess, time
p = Path('$HOME/trust-cg/target/zst-tuple-investigation')
root = p.parents[1]
cmd = ['python3', str(root/'target/main-alignment-20260929/workspace-tests.py'),
       'test', '-p', 'trust-cg-codegen', '--test', 'aarch64_compiler_jit_sealed_link',
       '--test', 'aarch64_checked_functions', '--no-run', '--message-format=json']
with (p/'jit-build-merged-1.log').open('wb') as f:
    r = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, timeout=900)
assert r.returncode == 0
events = []
for line in (p/'jit-build-merged-1.log').read_text().splitlines():
    try: events.append(json.loads(line))
    except ValueError: pass
assert any(e.get('reason') == 'build-finished' and e['success'] for e in events)
exec((p/'runtime-first.py').read_text().split('import hashlib')[0])
env['XDG_CACHE_HOME'] = '/tmp/trust-cg-borrowed-aggregate-proof-qjyzzw76'
rows = []
for name in ['aarch64_compiler_jit_sealed_link', 'aarch64_checked_functions']:
    artifacts = [e for e in events if e.get('reason') == 'compiler-artifact'
                 and e.get('target', {}).get('name') == name and e.get('executable')]
    assert len(artifacts) == 1
    original = Path(artifacts[0]['executable'])
    frozen = p / f'{name}-merged-1.test'
    shutil.copy2(original, frozen)
    command = [str(frozen), '--test-threads=1', '--nocapture']
    start = time.monotonic()
    with (p/f'{name}-merged-1.log').open('wb') as f:
        r = subprocess.run(command, env=env, stdout=f, stderr=subprocess.STDOUT, timeout=300)
    rows.append(dict(name=name, build_command=cmd, command=command,
                     executable_sha256=hashlib.sha256(frozen.read_bytes()).hexdigest(),
                     returncode=r.returncode, wall_seconds=time.monotonic()-start))
    (p/'jit-merged-1-results.json').write_text(json.dumps(rows, indent=2)+'\n')
    print(name, r.returncode, flush=True)
    assert r.returncode == 0
