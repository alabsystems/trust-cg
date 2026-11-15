from pathlib import Path
import gzip, hashlib, json, re

p = Path('$HOME/trust-cg/target/std-intrinsic-validity-investigation')
out = Path('$HOME/trust-cg/reports/perf/2026-09-29-intrinsic-validity')
out.mkdir(exist_ok=True)

def copy(src, name=None, compress=False):
    src = Path(src)
    name = name or src.name
    data = src.read_bytes()
    if compress:
        name += '.gz'
        data = gzip.compress(data, mtime=0)
    (out / name).write_bytes(data)

for label in ['first', 'merged-1']:
    for suffix in ['source-head.txt', 'source-manifest.json', 'source.patch', 'lib.rs']:
        copy(p / f'{label}-{suffix}', compress=suffix in ['source.patch', 'lib.rs'])
    for suffix in ['.py', '-receipt.json', '.log']:
        copy(p / f'build-{label}{suffix}', compress=suffix == '.log')
    copy(p / f'runtime-{label}.py')
for name in ['native-build-first-receipt.json', 'native-first-inputs.json',
             'test-build-first.py', 'std-delta-first.json', 'std-O0-first-results.json',
             'probe.py', 'corpus.rs', 'driver.rs', 'validity-corpus.rs',
             'validity-driver.rs', 'validity-driver-v2.rs', 'validity-probe.py',
             'validity-probe-v2.py', 'isolate.py', 'mixed-stdlib.py',
             'mixed-compiler-wrapper.py', 'dynamic-consumers.py', 'mixed-validity.py',
             'core-consumer.rs', 'core-driver.c', 'real-runtime.rs', 'mixed-core-panic.rs',
             'core-reference-format.rs', 'docs-merged-1.py']:
    copy(p / name)
for name in ['env.py', 'native-build-first.log', 'native-first.log',
             'native-residual-first.log', 'native-union-first.log',
             'docs-merged-1-run.log']:
    copy(p / name, compress=True)
copy(p / 'std-O0-first/compile.log', 'std-O0-first-compile.log', True)
copy(p.parent / 'std-completion-investigation/trust-ir-cohort-identity.json')
copy(p.parent / 'std-completion-investigation/std-O0-reference-second-results.json')
for name in ['intrinsic_validity.rs', 'intrinsic_validity_driver.rs']:
    copy(p.parents[1] / 'crates/rustc-codegen-trust-cg/tests/support/residual_conversion' / name)
copy(p.parents[1] / 'crates/rustc-codegen-trust-cg/tests/support/residual_conversion.rs', compress=True)

native_logs = [p / name for name in ['native-first.log', 'native-residual-first.log', 'native-union-first.log']]
texts = [f.read_text() for f in native_logs]
assert all('test result: ok.' in s for s in texts)
summary = {key: sum(int(n) for s in texts for n in re.findall(r'\b' + key + r'=(\d+)', s))
           for key in ['checks', 'executions', 'aborts', 'refusals']}
assert summary == dict(checks=4227072, executions=56, aborts=208, refusals=2), summary
(out / 'native-first-summary.json').write_text(json.dumps(summary, indent=2) + '\n')

for label in ['baseline', 'first', 'validity-baseline', 'validity-first',
              'validity-baseline-v2', 'validity-first-v2', 'validity-merged-1']:
    rows = json.loads((p / f'{label}-results.json').read_text())
    if label in ['validity-first-v2', 'validity-merged-1']:
        assert len(rows) == 24 and all(r['returncode'] == 0 for r in rows)
    copy(p / f'{label}-results.json')
    for row in rows:
        d = Path(row['directory'])
        copy(d / (row['step'] + '.log'), f'{d.name}-{row["step"]}.log', True)
copy(p / 'first-cg-O2/corpus.mir', 'zeroed-array-O2.mir', True)

for label in ['first', 'strict-init-first', 'merged-1', 'strict-init-merged-1']:
    rows = json.loads((p / f'proof-{label}-results.json').read_text())
    sums = []
    for row in rows:
        mode, opt = row['mode'], row['opt']
        f = p / f'proof-{label}-{mode}-O{opt}/compile.log'
        s = f.read_text()
        assert row['returncode'] == (0 if mode == 'strict' else 1)
        if mode == 'machine':
            assert 'TCG-PROOF-465' in s
        traces = re.findall(r': (\d+) refined, (\d+) skipped .*?, (\d+) memo-hit', s)
        vals = [sum(int(t[i]) for t in traces) for i in range(3)]
        unmodeled = sum(map(int, re.findall(r'; (\d+) unmodeled shape', s)))
        assert (len(traces), *vals, unmodeled) == ((20,14,0,1,0) if opt == 0 else (12,10,0,0,0))
        sums.append(dict(mode=mode,opt=opt,functions=len(traces),refined=vals[0],skipped=vals[1],memo_hits=vals[2],unmodeled=unmodeled))
        copy(f, f'proof-{label}-{mode}-O{opt}.log', True)
    (p / f'proof-{label}-summary.json').write_text(json.dumps(sums, indent=2) + '\n')
    for suffix in ['.py', '-results.json', '-summary.json', '-source.rs']:
        copy(p / f'proof-{label}{suffix}')

label = 'mixed-core-alloc-O2-first'
result = json.loads((p / f'{label}-results.json').read_text())
assert result['returncode'] == 0 and not result['timed_out']
copy(p / f'{label}-results.json')
copy(p / label / 'build.log', f'{label}-build.log', True)
for crate in ['core', 'alloc', 'std']:
    matches = []
    for f in (p / label / 'invocations').glob('*.json'):
        c = json.loads(f.read_text())['command']
        if '--crate-name' in c and c[c.index('--crate-name')+1] == crate and '--target' in c:
            matches.append(f)
    assert len(matches) == 1
    copy(matches[0], f'{label}-{crate}-invocation.json')
for kind in ['dynamic', 'validity']:
    rows = json.loads((p / f'{label}-{kind}-results.json').read_text())
    assert all(r['returncode'] == 0 for r in rows)
    for suffix in ['results.json', 'sysroot.json']:
        copy(p / f'{label}-{kind}-{suffix}')
    for row in rows:
        if row['step'] == 'native':
            d = Path(row['directory'])
            copy(d / 'native.log', f'{d.name}-native.log', True)

copy(p / 'README-report.md', 'README.md')
copy(p / 'report.py')
assets = {f.name: dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(), bytes=f.stat().st_size)
          for f in sorted(out.iterdir()) if f.name != 'assets.json'}
(out / 'assets.json').write_text(json.dumps(assets, indent=2) + '\n')
print(len(assets), 'evidence files')
