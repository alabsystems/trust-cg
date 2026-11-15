from pathlib import Path
import gzip, hashlib, json, re

p = Path('$HOME/trust-cg/target/zst-tuple-investigation')
old = p.parent / 'std-intrinsic-validity-investigation'
out = Path('$HOME/trust-cg/reports/perf/2026-09-29-zero-sized-tuples')
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
        assert (len(traces), *vals, unmodeled) == ((34,14,0,2,0) if opt == 0 else (29,17,0,6,0))
        sums.append(dict(mode=mode,opt=opt,functions=len(traces),refined=vals[0],skipped=vals[1],memo_hits=vals[2],unmodeled=unmodeled))
        copy(f, f'proof-{label}-{mode}-O{opt}.log', True)
    (p / f'proof-{label}-summary.json').write_text(json.dumps(sums, indent=2) + '\n')
    for suffix in ['.py', '-results.json', '-summary.json', '-source.rs']:
        copy(p / f'proof-{label}{suffix}')

for name in ['native-build-first-receipt.json', 'native-first-inputs.json',
             'test-build-first.py', 'native-first-summary.json', 'controls-first-results.json',
             'probe.py', 'corpus.rs', 'driver.rs', 'expanded-corpus.rs',
             'expanded-driver.rs', 'expanded-corpus-v2.rs', 'expanded-probe-v2.py',
             'zero_sized_drop.rs', 'overaligned.rs', 'qualify-jit-merged-1.py', 'jit-merged-1-results.json',
             'expanded-probe.py', 'isolate.py', 'mixed-stdlib.py',
             'mixed-compiler-wrapper.py', 'dynamic-consumers.py',
             'core-consumer.rs', 'core-driver.c', 'real-runtime.rs', 'mixed-core-panic.rs',
             'core-reference-format.rs', 'docs-merged-1.py']:
    copy(p / name)
for name in ['env.py', 'native-build-first.log', 'native-first.log', 'native-merged-1.log',
             'docs-merged-1-run.log', 'native-zero-sized-drop-merged-1.log', 'jit-build-merged-1.log',
             'aarch64_compiler_jit_sealed_link-merged-1.log', 'aarch64_checked_functions-merged-1.log']:
    copy(p / name, compress=True)
for row in json.loads((p / 'controls-first-results.json').read_text()):
    assert row['returncode'] == 0
    copy(row['log'], compress=True)
assert 'test result: ok.' in (p / 'native-merged-1.log').read_text()
for name in ['zero_sized_tuples.rs', 'zero_sized_tuples_driver.rs']:
    copy(p / name)
copy(p / 'permanent-harness.rs', 'residual_conversion.rs', compress=True)

for label in ['baseline', 'first', 'expanded-first', 'expanded-first-v2', 'expanded-baseline', 'expanded-baseline-v2']:
    rows = json.loads((p / f'{label}-results.json').read_text())
    if label in ['first', 'expanded-first-v2']:
        assert len(rows) == 12 and all(r['returncode'] == 0 for r in rows)
    copy(p / f'{label}-results.json')
    for row in rows:
        d = Path(row['directory'])
        copy(d / (row['step'] + '.log'), f'{d.name}-{row["step"]}.log', True)
copy(p / 'first-cg-O2/corpus.mir', 'zero-sized-tuples-O2.mir', True)

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
rows = json.loads((p / f'{label}-dynamic-results.json').read_text())
assert all(r['returncode'] == 0 for r in rows)
for suffix in ['results.json', 'sysroot.json']:
    copy(p / f'{label}-dynamic-{suffix}')
for row in rows:
    if row['step'] == 'native':
        d = Path(row['directory'])
        copy(d / 'native.log', f'{d.name}-native.log', True)

copy(p / 'README-report.md', 'README.md')
assert all(r['returncode'] == 0 for r in json.loads((p/'jit-merged-1-results.json').read_text()))
assert 'test result: ok.' in (p/'native-zero-sized-drop-merged-1.log').read_text()
copy(p / 'report.py')
assets = {f.name: dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(), bytes=f.stat().st_size)
          for f in sorted(out.iterdir()) if f.name != 'assets.json'}
(out / 'assets.json').write_text(json.dumps(assets, indent=2) + '\n')
print(len(assets), 'evidence files')
