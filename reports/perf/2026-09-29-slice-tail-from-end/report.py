from pathlib import Path
import json,hashlib,gzip
p=Path('$HOME/trust-cg/target/slice-from-end-investigation');out=p.parents[1]/'reports/perf/2026-09-29-slice-tail-from-end'
assert not out.exists() or set(x.name for x in out.iterdir())=={'README.md'}
out.mkdir(exist_ok=True)
def copy(src,name=None):
 src=Path(src);name=name or src.name;b=src.read_bytes()
 if src.suffix in ['.log','.patch'] or name.endswith(('manifest.json','inputs.json')):name+='.gz';b=gzip.compress(b,mtime=0)
 assert not (out/name).exists() or (name=='README.md' and (out/name).read_bytes()==b),name
 (out/name).write_bytes(b)
for label in ['first','second','third','merged']:
 for suffix in ['source-head.txt','source.patch','source-manifest.json']:copy(p/f'{label}-{suffix}')
 for suffix in ['.py','.log']:copy(p/f'build-{label}{suffix}')
 if label!='second':copy(p/f'build-{label}-receipt.json')
 if label!='first':copy(p/f'{label}-slice_tail.rs')
for label in ['third','merged']:
 for suffix in ['.py','-results.json','-summary.json']:copy(p/f'native-{label}{suffix}')
 copy(p/f'runtime-{label}.py')
 for row in json.loads((p/f'native-{label}-results.json').read_text()):assert row['returncode']==0;copy(row['log'])
 for suffix in ['.py','-results.json','-summary.json','-source.rs']:copy(p/f'proof-{label}{suffix}')
 for row in json.loads((p/f'proof-{label}-results.json').read_text()):
  mode,opt=row['mode'],row['opt'];assert row['returncode']==(0 if mode=='strict' else 1);copy(p/f'proof-{label}-{mode}-O{opt}/compile.log',f'proof-{label}-{mode}-O{opt}.log')
for name in ['env.py','corpus.rs','driver.rs','wrapped-corpus.rs','wrapped-driver.rs','expanded-corpus.rs','expanded-driver.rs','projected-field-negative.rs','probe.py','wrapped-probe.py','expanded-probe.py','test-build-first.py','native-build-first.log','native-build-first-receipt.json','native-first-inputs.json','qualify-merged.py','root-build-merged.log','root-build-merged-receipt.json','root-merged-results.json','root-merged-inputs.json','summarize.py','isolate.py','std-O2-baseline-results.json','std-O2-third-results.json','std-delta.py','std-delta-third.json','baseline-census-agreement.json','std-census-comparison.json','mixed-stdlib.py','mixed-compiler-wrapper.py','dynamic-consumers.py','core-consumer.rs','core-driver.c','real-runtime.rs','mixed-core-panic.rs','core-reference-format.rs','docs.py','docs-run.log','docs-check.log','diagnostics-check.log','linux-floor-list.log']:
 copy(p/name)
for f in p.glob('permanent-*'):copy(f)
for label in ['baseline','first','third','wrapped-baseline','wrapped-first','wrapped-third','expanded-baseline','expanded-first','expanded-third']:
 copy(p/f'{label}-results.json')
 for row in json.loads((p/f'{label}-results.json').read_text()):
  d=Path(row['directory']);copy(d/(row['step']+'.log'),d.name+'-'+row['step']+'.log')
# The first prototype was ineffective at O2; preserve its strict diagnostics too.
for suffix in ['.py','-results.json','-source.rs']:copy(p/f'proof-first{suffix}')
for row in json.loads((p/'proof-first-results.json').read_text()):
 mode,opt=row['mode'],row['opt'];copy(p/f'proof-first-{mode}-O{opt}/compile.log',f'proof-first-{mode}-O{opt}.log')
for row in json.loads((p/'root-merged-results.json').read_text()):assert row['returncode']==0;copy(row['log'])
for label in ['baseline','third']:copy(p/f'std-O2-{label}/compile.log',f'std-O2-{label}-compile.log')
old=p.parent/'fat-fn-spread-investigation'
for suffix in ['source-head.txt','source.patch','source-manifest.json']:copy(old/f'merged-2-{suffix}',f'baseline-{suffix}')
copy(old/'build-merged-2-receipt.json','baseline-build-receipt.json')
label='mixed-core-alloc-third-O2';d=json.loads((p/f'{label}-results.json').read_text());assert d['returncode']==0 and not d['timed_out']
copy(p/f'{label}-results.json');copy(p/label/'build.log',f'{label}-build.log')
for crate in ['core','alloc','std']:
 fs=[]
 for f in (p/label/'invocations').glob('*.json'):
  cmd=json.loads(f.read_text())['command']
  if '--crate-name' in cmd and cmd[cmd.index('--crate-name')+1]==crate and '--target' in cmd:fs.append(f)
 assert len(fs)==1;copy(fs[0],f'{label}-{crate}-invocation.json')
for suffix in ['results.json','sysroot.json']:copy(p/f'{label}-dynamic-{suffix}')
for row in json.loads((p/f'{label}-dynamic-results.json').read_text()):
 assert row['returncode']==0
 if row['step']=='native':
  d=Path(row['directory']);copy(d/'native.log',d.name+'-native.log')
copy(p/'README-report.md','README.md');copy(p/'report.py')
assets={f.name:dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size) for f in sorted(out.iterdir()) if f.name!='assets.json'}
(out/'assets.json').write_text(json.dumps(assets,indent=2)+'\n');print(len(assets),'assets',sum(m['bytes'] for m in assets.values()))
