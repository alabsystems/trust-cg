from pathlib import Path
import gzip,hashlib,json,re
p=Path('$HOME/trust-cg/target/fat-fn-spread-investigation')
out=p.parents[1]/'reports/perf/2026-09-29-fat-fn-arguments'
assert not out.exists() or set(x.name for x in out.iterdir())=={'README.md'}, 'published reports are immutable'
out.mkdir(exist_ok=True)
def copy(src,name=None,compress=None):
 src=Path(src);name=name or src.name;data=src.read_bytes()
 if compress is None:compress=src.suffix in ['.log','.patch'] or src.name.endswith('-lib.rs')
 if compress:name+='.gz';data=gzip.compress(data,mtime=0)
 assert not (out/name).exists() or (name=='README.md' and (out/name).read_bytes()==data),name
 (out/name).write_bytes(data)
for label in ['first','merged']:
 for suffix in ['source-head.txt','source.patch','source-manifest.json','lib.rs']:copy(p/f'{label}-{suffix}')
 for suffix in ['.py','.log','-receipt.json']:copy(p/f'build-{label}{suffix}')
 for suffix in ['.py','-results.json','-summary.json']:copy(p/f'native-{label}{suffix}')
 copy(p/f'runtime-{label}.py')
 for row in json.loads((p/f'native-{label}-results.json').read_text()):
  assert row['returncode']==0;copy(row['log'])
 for suffix in ['.py','-results.json','-source.rs','-summary.json']:copy(p/f'proof-{label}{suffix}')
 for row in json.loads((p/f'proof-{label}-results.json').read_text()):
  mode,opt=row['mode'],row['opt'];copy(p/f'proof-{label}-{mode}-O{opt}/compile.log',f'proof-{label}-{mode}-O{opt}.log')
for name in ['env.py','corpus.rs','driver.rs','expanded-corpus.rs','expanded-driver.rs','constant-corpus.rs','constant-driver.rs','callee-corpus.rs','callee-driver.rs','box-corpus.rs','box-driver.rs','probe.py','expanded-probe.py','constant-probe.py','callee-probe.py','box-probe.py','test-build-first.py','native-build-first.log','native-build-first-receipt.json','native-first-inputs.json','qualify-merged.py','root-build-merged.log','root-build-merged-receipt.json','root-merged-results.json','root-merged-inputs.json','summarize.py','isolate.py','std-O2-baseline-results.json','std-O2-first-results.json','std-delta.py','std-delta-first.json','std-census-comparison.json','mixed-stdlib.py','mixed-compiler-wrapper.py','dynamic-consumers.py','core-consumer.rs','core-driver.c','real-runtime.rs','mixed-core-panic.rs','core-reference-format.rs','mixed-first-scope-note.txt','mixed-first-O2-results.json','docs.py','docs-run.log','docs-check.log','diagnostics-check.log','linux-floor-list.log']:
 copy(p/name)
for f in p.glob('permanent-*'):copy(f)
for label in ['baseline','first','expanded-baseline','expanded-first','constant-baseline','constant-first','callee-baseline','callee-first','box-baseline','box-first']:
 copy(p/f'{label}-results.json')
 for row in json.loads((p/f'{label}-results.json').read_text()):
  d=Path(row['directory']);copy(d/(row['step']+'.log'),d.name+'-'+row['step']+'.log')
for row in json.loads((p/'root-merged-results.json').read_text()):assert row['returncode']==0;copy(row['log'])
for label in ['baseline','first']:copy(p/f'std-O2-{label}/compile.log',f'std-O2-{label}-compile.log')
# Pin the before artifact and its source inputs alongside the paired census.
old=p.parent/'virtual-unwind-investigation'
for suffix in ['source-head.txt','source.patch','source-manifest.json']:copy(old/f'merged-2-{suffix}',f'baseline-{suffix}')
copy(old/'build-merged-2-receipt.json','baseline-build-receipt.json')
copy(p/'mixed-first-O2/build.log','mixed-first-O2-build.log')
label='mixed-core-alloc-first-O2'
x=json.loads((p/f'{label}-results.json').read_text());assert x['returncode']==0 and not x['timed_out']
copy(p/f'{label}-results.json');copy(p/label/'build.log',label+'-build.log')
for crate in ['core','alloc','std']:
 fs=[]
 for f in (p/label/'invocations').glob('*.json'):
  c=json.loads(f.read_text())['command']
  if '--crate-name' in c and c[c.index('--crate-name')+1]==crate and '--target' in c:fs.append(f)
 assert len(fs)==1;copy(fs[0],f'{label}-{crate}-invocation.json')
for suffix in ['results.json','sysroot.json']:copy(p/f'{label}-dynamic-{suffix}')
for row in json.loads((p/f'{label}-dynamic-results.json').read_text()):
 assert row['returncode']==0
 if row['step']=='native':
  d=Path(row['directory']);copy(d/'native.log',d.name+'-native.log')
copy(p/'README-report.md','README.md',False);copy(p/'report.py')
assets={f.name:dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size) for f in sorted(out.iterdir()) if f.name!='assets.json'}
(out/'assets.json').write_text(json.dumps(assets,indent=2)+'\n')
print(len(assets),'evidence files',sum(x['bytes'] for x in assets.values()))
