from pathlib import Path
import gzip,hashlib,json,re
p=Path('$HOME/trust-cg/target/virtual-unwind-investigation')
out=p.parents[1]/'reports/perf/2026-09-29-virtual-unwind-filters'
out.mkdir(exist_ok=True)
def copy(src,name=None,compress=None):
 src=Path(src);name=name or src.name;data=src.read_bytes()
 if compress is None:compress=src.suffix in ['.log','.patch'] or src.name.endswith('-lib.rs')
 if compress:name+='.gz';data=gzip.compress(data,mtime=0)
 (out/name).write_bytes(data)
for label in ['first','second','third','merged-1']:
 for suffix in ['source-head.txt','source.patch','source-manifest.json','lib.rs']:copy(p/f'{label}-{suffix}')
 for suffix in ['.py','.log','-receipt.json']:copy(p/f'build-{label}{suffix}')
for name in ['corpus.rs','driver.rs','expanded-corpus.rs','expanded-driver.rs','expanded-driver-v2.rs','expanded-driver-hooks.rs','forced.c','forced-driver.rs','probe.py','expanded-probe.py','expanded-probe-v2.py','forced-probe.py','env.py','hooks-results.json','terminate-debug.gdb','terminate-pad-debug.gdb','personality-debug.gdb','personality-region-debug.gdb','terminate-disassembly.txt','ir-cohort-comparison.json','native-first-inputs.json','native-build-first-receipt.json','test-build-first.py','native-build-first.log','root-build-first.py','root-build-first-receipt.json','root-tests-first.py','root-first-results.json','root-first-inputs.json','root-first-source-head.txt','root-first-source.patch','root-first-rust_empty_filter.rs','lower-first-results.json','lower-first-tests.log','root-build-merged-1.py','root-build-merged-1-receipt.json','root-tests-merged-1.py','root-merged-1-results.json','root-merged-1-inputs.json','isolate.py','std-delta.py','std-delta-third.json','std-O2-third-results.json','mixed-stdlib.py','mixed-compiler-wrapper.py','dynamic-consumers.py','core-consumer.rs','core-driver.c','real-runtime.rs','mixed-core-panic.rs','core-reference-format.rs','docs-merged-1.py','docs-merged-1-run.log','docs-final-run.log','linux-floor-list.log']:
 copy(p/name)
for pattern in ['permanent-*','terminate-gdb-*.log','terminate-pad-gdb.log','personality-gdb-*.log','personality-region-*.log','hooks-*.log','root-*-build.log','root-*-build-merged-1.log','docs-check-merged-1.log','diagnostics-check-merged-1.log']:
 for f in sorted(p.glob(pattern)):copy(f)
for label in ['baseline','first','expanded-second','expanded-v2-second','expanded-v2-third','forced-second','forced-third']:
 rows=json.loads((p/f'{label}-results.json').read_text());copy(p/f'{label}-results.json')
 for row in rows:
  d=Path(row['directory']);copy(d/(row['step']+'.log'),d.name+'-'+row['step']+'.log')
for label in ['third','merged-1']:
 copy(p/f'runtime-{label}.py');copy(p/f'native-{label}.py');copy(p/f'native-{label}-results.json');copy(p/f'native-{label}-summary.json')
 rows=json.loads((p/f'native-{label}-results.json').read_text());assert len(rows)==4 and all(r['returncode']==0 for r in rows)
 for row in rows:copy(row['log'])
 for suffix in ['.py','-results.json','-source.rs']:copy(p/f'proof-{label}{suffix}')
 rows=json.loads((p/f'proof-{label}-results.json').read_text());sums=[]
 for row in rows:
  mode,opt=row['mode'],row['opt'];f=p/f'proof-{label}-{mode}-O{opt}/compile.log';s=f.read_text();traces=re.findall(r': (\d+) refined, (\d+) skipped .*?, (\d+) memo-hit',s);vals=[sum(int(t[i]) for t in traces) for i in range(3)];unmodeled=sum(map(int,re.findall(r'; (\d+) unmodeled shape',s)))
  assert row['returncode']==(0 if mode=='strict' else 1)
  if mode=='machine':assert 'TCG-PROOF-465' in s
  assert (len(traces),*vals,unmodeled)==((18,16,0,1,0) if opt==0 else (15,13,0,1,0))
  sums.append(dict(mode=mode,opt=opt,functions=len(traces),refined=vals[0],skipped=vals[1],memo_hits=vals[2],unmodeled=unmodeled));copy(f,f'proof-{label}-{mode}-O{opt}.log')
 (out/f'proof-{label}-summary.json').write_text(json.dumps(sums,indent=2)+'\n')
for label in ['first','merged-1']:
 for row in json.loads((p/f'root-{label}-results.json').read_text()):assert row['returncode']==0;copy(row['log'])
copy(p/'std-O2-third/compile.log','std-O2-third-compile.log')
copy(p.parent/'zst-tuple-investigation/std-O2-first-results.json','std-before-results.json')
copy(p.parent/'zst-tuple-investigation/first-source-manifest.json','std-before-source-manifest.json')
label='mixed-core-alloc-O2-third'
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
