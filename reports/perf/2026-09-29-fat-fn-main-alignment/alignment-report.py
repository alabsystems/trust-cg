from pathlib import Path
import json,hashlib,gzip
p=Path('$HOME/trust-cg/target/fat-fn-spread-investigation');out=p.parents[1]/'reports/perf/2026-09-29-fat-fn-main-alignment'
assert not out.exists();out.mkdir()
def copy(src,name=None):
 src=Path(src);name=name or src.name;b=src.read_bytes()
 if src.suffix in ['.log','.patch'] or src.name.endswith('-lib.rs'):name+='.gz';b=gzip.compress(b,mtime=0)
 assert not (out/name).exists();(out/name).write_bytes(b)
for label in ['merged-2']:
 for suffix in ['source-head.txt','source.patch','source-manifest.json','lib.rs']:copy(p/f'{label}-{suffix}')
 for suffix in ['.py','.log','-receipt.json']:copy(p/f'build-{label}{suffix}')
 for suffix in ['.py','-results.json','-summary.json']:copy(p/f'native-{label}{suffix}')
 copy(p/f'runtime-{label}.py')
 for row in json.loads((p/f'native-{label}-results.json').read_text()):assert row['returncode']==0;copy(row['log'])
 for suffix in ['.py','-results.json','-summary.json','-source.rs']:copy(p/f'proof-{label}{suffix}')
 for row in json.loads((p/f'proof-{label}-results.json').read_text()):
  mode,opt=row['mode'],row['opt'];assert row['returncode']==(0 if mode=='strict' else 1);copy(p/f'proof-{label}-{mode}-O{opt}/compile.log',f'proof-{label}-{mode}-O{opt}.log')
for name in ['qualify-merged-2.py','root-build-merged-2.log','root-build-merged-2-receipt.json','root-merged-2-results.json','root-merged-2-inputs.json','python-merged-2.log','python-merged-2-fixed.log','host-matrix-merged-2.log','inventory-commit.log','docs-alignment-run.log','docs-check.log','diagnostics-check.log','overflow-merged-2.py','overflow-build-merged-2.log','overflow-build-merged-2-receipt.json','overflow-merged-2.log','overflow-merged-2-results.json','overflow-comparison.py','overflow-comparison-results.json','overflow-comparison-summary.json','overflow-comparison-before.log','overflow-comparison-after.log']:
 copy(p/name)
for row in json.loads((p/'root-merged-2-results.json').read_text()):assert row['returncode']==0;copy(row['log'])
for f in p.glob('overflow-baseline*'):
 if f.suffix in ['.log','.json','.py']:copy(f)
copy(p/'README-alignment.md','README.md');copy(p/'alignment-report.py')
assets={f.name:dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size) for f in sorted(out.iterdir())}
(out/'assets.json').write_text(json.dumps(assets,indent=2)+'\n');print(len(assets),sum(m['bytes'] for m in assets.values()))
