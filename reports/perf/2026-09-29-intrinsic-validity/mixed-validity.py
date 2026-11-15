from pathlib import Path
import hashlib, json, os, subprocess, sys, time

p = Path('$HOME/trust-cg/target/std-intrinsic-validity-investigation')
exec((p / 'env.py').read_text())
label = sys.argv[1]
backend = Path(sys.argv[2]).resolve()
result = json.loads((p / f'{label}-results.json').read_text())
assert result['returncode'] == 0 and not result['timed_out']
deps = p / label / 'target/aarch64-unknown-linux-gnu/debug/deps'
sysroot = p / f'{label}-validity-sysroot'
libdir = sysroot / 'lib/rustlib/aarch64-unknown-linux-gnu/lib'
libdir.mkdir(parents=True, exist_ok=True)

def sha(f):
    return hashlib.sha256(f.read_bytes()).hexdigest()

libs = []
for source in sorted(deps.iterdir()):
    if source.suffix not in ['.rlib', '.so']:
        continue
    dest = libdir / source.name
    if not dest.exists():
        dest.symlink_to(source)
    assert dest.resolve() == source.resolve()
    libs.append(dict(name=source.name, source=str(source), sha256=sha(source)))
assert any(row['name'] == 'libstd.so' for row in libs)
(p / f'{label}-validity-sysroot.json').write_text(json.dumps(libs, indent=2) + '\n')
rows = []

def run(d, step, command):
    selected = env.copy()
    if step == 'native':
        selected.update(LD_LIBRARY_PATH=str(libdir) + ':' + env['LD_LIBRARY_PATH'], LD_DEBUG='libs')
        command = ['sh', '-c', 'ulimit -c 0; exec "$@"', 'validity-mixed', *command]
    start = time.monotonic()
    with (d / f'{step}.log').open('wb') as log:
        result = subprocess.run(command, env=selected, stdout=log, stderr=subprocess.STDOUT, timeout=180)
    rows.append(dict(directory=str(d), step=step, command=command, returncode=result.returncode,
                     wall_seconds=time.monotonic() - start, backend_sha256=sha(backend),
                     environment={k: selected[k] for k in ['LD_LIBRARY_PATH', 'LD_DEBUG'] if k in selected}))
    (p / f'{label}-validity-results.json').write_text(json.dumps(rows, indent=2) + '\n')
    print(d.name, step, result.returncode, flush=True)
    return result.returncode

for strict in [False, True]:
    for lane in ['llvm', 'cg']:
        d = p / f'{label}-validity-strict{int(strict)}-{lane}'
        d.mkdir(exist_ok=True)
        command = [str(tc / 'bin/trustc'), '--sysroot', str(sysroot), '--edition=2024',
                   '--crate-type=lib', '--emit=obj', '-Copt-level=0', '-Cpanic=unwind',
                   '-Ccodegen-units=1', '-Ztrust-verify=off', str(p / 'validity-corpus.rs'),
                   '--out-dir', str(d)]
        if strict:
            command += ['-Zstrict-init-checks=yes']
        if lane == 'cg':
            command += ['-Zcodegen-backend=' + str(backend), '-Ztrust-ir-cg-args=diag-json no-proof-certs']
        if run(d, 'compile', command):
            continue
        command = [str(tc / 'bin/trustc'), '--sysroot', str(sysroot), '--edition=2024',
                   '-Cprefer-dynamic', '-Cpanic=unwind', '-Ztrust-verify=off',
                   str(p / 'validity-driver-v2.rs'),
                   *['-Clink-arg=' + str(f) for f in sorted(d.glob('*.o'))], '-o', str(d / 'native.elf')]
        if strict:
            command += ['--cfg=strict_init']
        if run(d, 'link', command):
            continue
        run(d, 'native', [str(d / 'native.elf')])

assert all(sha(Path(row['source'])) == row['sha256'] for row in libs)
assert sum(row['step'] == 'native' for row in rows) == 4
raise SystemExit(0 if all(row['returncode'] == 0 for row in rows) else 1)
