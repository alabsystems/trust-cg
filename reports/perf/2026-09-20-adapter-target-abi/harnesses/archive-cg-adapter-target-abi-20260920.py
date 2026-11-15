from pathlib import Path
import gzip,hashlib,json,re,subprocess
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-abi-target-20260920');run=r/'cg-adapter-target-abi-floor-first'
floor=json.loads((run/'results.json').read_text());assert floor['complete'] and floor['passed']
assert floor['source_unchanged'] and floor['tools_unchanged'] and not floor['dependency_changes']
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()==floor['provenance']['source_sha']
assert not subprocess.check_output(['git','status','--porcelain'],cwd=p,text=True).strip()
qualification=json.loads((r/'cg-adapter-target-abi-targeted-complete.json').read_text());assert qualification['passed']
selected=[];tests=0;qualified_source=None
for label in qualification['completed']:
 folder=r/('cg-adapter-target-abi-'+label);record=json.loads((folder/'result.json').read_text());assert record['passed'] and record['source_unchanged']
 if qualified_source is None:qualified_source=record['source']
 assert record['source']['source_fingerprint']==qualified_source['source_fingerprint']
 log=(folder/'command.log').read_text();counts=re.findall(r'test result: ok\. (\d+) passed; (\d+) failed; (\d+) ignored;',log)
 assert counts and all(int(failed)==int(ignored)==0 for _,failed,ignored in counts)
 tests+=sum(int(passed) for passed,_,_ in counts);selected.append(folder)
assert tests==29
assert hashlib.sha256((r/'adapter-target-abi-candidate-third.patch').read_bytes()).hexdigest()==qualified_source['tracked_diff_sha256']
committed_patch=subprocess.check_output(['git','diff','--binary','--no-ext-diff','--no-textconv',qualified_source['source_sha'],'HEAD','--'],cwd=p)
assert hashlib.sha256(committed_patch).hexdigest()==qualified_source['tracked_diff_sha256']
assert 'I128_NARROW_ABI opt_levels=4 native_calls=384' in (r/'cg-adapter-target-abi-native-first/command.log').read_text()
assert json.loads((r/'cg-adapter-target-abi-baseline-fourth-observation.json').read_text())['expected_regression_observed']
def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as file:
  while chunk:=file.read(1024*1024):h.update(chunk)
 return h.hexdigest()
binaries=[]
for folder in [run,*selected]:
 for log in sorted(folder.glob('*.log')):
  for name in re.findall(r'^\s*Running .+? \(([^\n]+)\)$',log.read_text(),re.M):
   binary=Path(name);binary=binary if binary.is_absolute() else p/binary;assert binary.is_file()
   binaries.append(dict(log=str(log.relative_to(r)),path=str(binary),sha256=digest(binary),bytes=binary.stat().st_size))
(run/'binaries.json').write_text(json.dumps(binaries,indent=2)+'\n')
out=p/'reports/perf/2026-09-20-adapter-target-abi';out.mkdir();artifacts=[]
def copy(source,name):
 raw=source.read_bytes();compress=source.suffix in ['.log','.patch','.rs'] or len(raw)>16000
 data=gzip.compress(raw,mtime=0) if compress else raw;name+='.gz' if compress else ''
 dest=out/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 row=dict(path=name,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
 if compress:row.update(stored_sha256=hashlib.sha256(data).hexdigest(),stored_bytes=len(data))
 artifacts.append(row)
folders=[run,*selected,r/'cg-adapter-target-abi-adapter-first']+[r/('cg-adapter-target-abi-baseline-'+ordinal) for ordinal in ['first','second','third','fourth']]
for folder in folders:
 for source in sorted(folder.rglob('*')):
  if source.is_file():copy(source,'records/'+str(source.relative_to(r)))
for pattern in ['adapter-target-abi-gate-tests-*.log','adapter-target-abi-candidate-*.patch','adapter-target-abi-baseline-fixture-*.rs','cg-adapter-target-abi-baseline*-observation.json','adapter-target-abi-*.log','adapter-target-abi-candidate-first-files.json','cg-adapter-target-abi-targeted-complete.json']:
 for source in sorted(r.glob(pattern)):
  name='harnesses/'+source.name
  if not any(row['path'] in [name,name+'.gz'] for row in artifacts):copy(source,name)
copy(r/'adapter-target-abi-baseline-source/crates/trust-cg-lower/tests/aarch64_adapter_target_abi.rs','harnesses/baseline-fixture-first.rs')
for name in ['run-cg-adapter-target-abi-check-20260920.py','run-cg-adapter-target-abi-baseline-20260920.py','qualify-cg-adapter-target-abi-floor-20260920.py','qualify-adapter-abi-targeted-20260920.py','qualify-adapter-abi-targeted-second-20260920.py','prepare-adapter-abi-baseline-after-floor-20260920.py','qualify-adapter-abi-after-baseline-20260920.py','run-command-to-log.py','archive-cg-adapter-target-abi-20260920.py','cg-adapter-target-abi-floor-first.log']:
 copy(r/name,'harnesses/'+name)
copy(Path('/home/ayates/ay-pblendvb-repair-20260914/scripts/_oom_guard.py'),'harnesses/_oom_guard.py')
for name in ['check_linux_aarch64.py','check_darwin_aarch64.py','run_with_timeout.py','dependency_identity.py']:
 copy(p/'scripts'/name,'gate-source/'+name)
(out/'inventory.json').write_text(json.dumps(dict(artifacts=artifacts),indent=2)+'\n')
total=sum(t.get('counts',{}).get('passed',0) for t in floor['targets'])
text=(r/'cg-adapter-target-abi-report.md').read_text().replace('@SOURCE@',floor['provenance']['source_sha']).replace('@TESTS@',str(total))
(out/'README.md').write_text(text)
subprocess.run(['python3','scripts/check_evidence_archive.py',str(out)],cwd=p,check=True)
print(json.dumps(dict(report=str(out),artifacts=len(artifacts),targets=len(floor['targets']),tests=total,targeted_tests=tests)),flush=True)
