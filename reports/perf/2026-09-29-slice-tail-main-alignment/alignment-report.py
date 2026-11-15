from pathlib import Path
import json,hashlib,gzip
p=Path('$HOME/trust-cg/target/slice-from-end-investigation')
out=p.parents[1]/'reports/perf/2026-09-29-slice-tail-main-alignment'
assert not out.exists() or set(f.name for f in out.iterdir())=={'README.md'}
readme=(p/'README-alignment.md').read_text();assert 'PLACEHOLDER' not in readme
out.mkdir(exist_ok=True)
def copy(src,name=None):
    src=Path(src);name=name or src.name;b=src.read_bytes()
    if src.suffix in ['.log','.patch'] or name.endswith(('manifest.json','inputs.json')):name+='.gz';b=gzip.compress(b,mtime=0)
    assert not (out/name).exists() or (name=='README.md' and (out/name).read_bytes()==b),name
    (out/name).write_bytes(b)
for label in ['merged-2','merged-3']:
    for suffix in ['source-head.txt','source.patch','source-manifest.json','slice_tail.rs']:copy(p/f'{label}-{suffix}')
    for suffix in ['.py','.log','-receipt.json']:copy(p/f'build-{label}{suffix}')
    for suffix in ['.py','-results.json','-summary.json']:copy(p/f'native-{label}{suffix}')
    copy(p/f'runtime-{label}.py')
    rows=json.loads((p/f'native-{label}-results.json').read_text());assert len(rows)==5
    for row in rows:assert row['returncode']==0;copy(row['log'])
    for suffix in ['.py','-results.json','-summary.json','-source.rs']:copy(p/f'proof-{label}{suffix}')
    for row in json.loads((p/f'proof-{label}-results.json').read_text()):
        mode,opt=row['mode'],row['opt'];assert row['returncode']==(0 if mode=='strict' else 1)
        copy(p/f'proof-{label}-{mode}-O{opt}/compile.log',f'proof-{label}-{mode}-O{opt}.log')
    for prefix,suffix in [('qualify-','.py'),('root-build-','.log'),('root-build-','-receipt.json'),('root-','-inputs.json'),('root-','-results.json')]:copy(p/f'{prefix}{label}{suffix}')
    for row in json.loads((p/f'root-{label}-results.json').read_text()):
        assert row['returncode']==(101 if label=='merged-3' else 0);copy(row['log'])
for name in ['env.py','workspace-online.py','summarize-alignment.py','root-alignment-summary.json','root-alignment-3-summary.json','qualify-alignment-extra.py','root-extra-build.log','root-extra-build-receipt.json','root-extra-results.json','root-extra-ub-map.log','root-extra-cse-opt-in.log','bridge-unit-alignment.py','bridge-unit-alignment-build.log','bridge-unit-alignment-receipt.json','bridge-unit-alignment-results.json','bridge-unit-alignment.log','alignment-python.log','alignment-python-corrected.log','alignment-tuple-check.log','alignment-trust-ir-source.patch','alignment-next-shared-source.json','alignment-source-stability.json','alignment-docs.py','alignment-docs-run.log','alignment-docs-check.log','alignment-diagnostics-check.log','alignment-3-docs.py','alignment-3-docs-run.log','alignment-3-docs-check.log','alignment-3-diagnostics-check.log','isolate.py','std-O2-merged-2-results.json','std-census-alignment.json','alignment-report.py']:
    copy(p/name)
for part in ['remaining','last']:
    copy(p/f'qualify-merged-3-{part}.py');copy(p/f'root-merged-3-{part}-results.json')
    for row in json.loads((p/f'root-merged-3-{part}-results.json').read_text()):
        expected=101 if Path(row['log']).name=='root-loop-symexec-merged-3.log' else 0
        assert row['returncode']==expected;copy(row['log'])
for label in ['x86-body','x86-credit','euclid']:
    copy(p/f'root-{label}-pre-merge.log');copy(p/f'root-{label}-pre-merge-results.json')
for label in ['affine-corrected','affine-actual']:
    copy(p/f'root-{label}-merged-3.log');copy(p/f'root-{label}-merged-3-results.json')
copy(p/'root-proof-gap-comparison.json')
copy(p/'std-O2-merged-2/compile.log','std-O2-merged-2-compile.log')
copy(p/'README-alignment.md','README.md')
assets={f.name:dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size) for f in sorted(out.iterdir()) if f.name!='assets.json'}
(out/'assets.json').write_text(json.dumps(assets,indent=2)+'\n')
for name,m in assets.items():
    b=(out/name).read_bytes();assert hashlib.sha256(b).hexdigest()==m['sha256']
    if name.endswith('.gz'):gzip.decompress(b)
print(len(assets),'assets',sum(m['bytes'] for m in assets.values()))
