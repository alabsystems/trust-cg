from pathlib import Path
import json,gzip,hashlib
p=Path('$HOME/trust-cg/target/slice-from-end-investigation');out=p.parents[1]/'reports/perf/2026-09-29-slice-tail-sync'
assert not out.exists() or set(f.name for f in out.iterdir())=={'README.md'}
assert 'PLACEHOLDER' not in (p/'README-sync.md').read_text()
out.mkdir(exist_ok=True)
def copy(src,name=None):
    src=Path(src);name=name or src.name;b=src.read_bytes()
    if src.suffix in ['.log','.patch'] or name.endswith(('manifest.json','inputs.json')):name+='.gz';b=gzip.compress(b,mtime=0)
    assert not (out/name).exists() or (name=='README.md' and (out/name).read_bytes()==b)
    (out/name).write_bytes(b)
for name in ['merged-4-source-head.txt','merged-4-source.patch','merged-4-source-manifest.json','merged-4-slice_tail.rs','build-merged-4.py','build-merged-4.log','build-merged-4-receipt.json','qualify-merged-4.py','root-build-merged-4.log','root-build-merged-4-receipt.json','root-merged-4-inputs.json','root-merged-4-results.json','bridge-unit-alignment-4.py','bridge-unit-alignment-4-build.log','bridge-unit-alignment-4-receipt.json','bridge-unit-alignment-4-results.json','bridge-unit-alignment-4.log','runtime-merged-4.py','native-from-end-merged-4.log','native-from-end-merged-4-results.json','proof-merged-4.py','proof-merged-4-source.rs','proof-merged-4-results.json','proof-merged-4-summary.json','sync-final-summary.json','sync-attempt-first.json','alignment-4-docs.py','alignment-4-docs-run.log','alignment-4-docs-check.log','alignment-4-diagnostics-check.log','env.py','sync-report-assets.py']:
    copy(p/name)
for row in json.loads((p/'root-merged-4-results.json').read_text()):assert row['returncode']==0;copy(row['log'])
for row in json.loads((p/'proof-merged-4-results.json').read_text()):
    mode,opt=row['mode'],row['opt'];assert row['returncode']==(0 if mode=='strict' else 1)
    copy(p/f'proof-merged-4-{mode}-O{opt}/compile.log',f'proof-merged-4-{mode}-O{opt}.log')
for name in ['merged-5-source-head.txt','merged-5-source.patch','qualify-merged-5.py','root-build-merged-5.log','root-build-merged-5-receipt.json','root-merged-5-inputs.json','root-merged-5-results.json','root-merged-5-summary.json','alignment-5-docs.py','alignment-5-docs-run.log','alignment-5-docs-check.log','alignment-5-diagnostics-check.log']:
    copy(p/name)
for row in json.loads((p/'root-merged-5-results.json').read_text()):assert row['returncode']==0;copy(row['log'])
copy(p/'README-sync.md','README.md')
assets={f.name:dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size) for f in sorted(out.iterdir()) if f.name!='assets.json'}
(out/'assets.json').write_text(json.dumps(assets,indent=2)+'\n')
for name,m in assets.items():
    b=(out/name).read_bytes();assert hashlib.sha256(b).hexdigest()==m['sha256']
    if name.endswith('.gz'):gzip.decompress(b)
print(len(assets),'assets',sum(m['bytes'] for m in assets.values()))
