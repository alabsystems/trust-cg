from pathlib import Path
import gzip,hashlib,json,re,subprocess,time
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-module-receipt-20260920');run=r/'cg-module-receipt-floor-second'
deadline=time.monotonic()+1800
while True:
 record=json.loads((run/'results.json').read_text())
 if record['complete']:break
 assert time.monotonic()<deadline
 time.sleep(5)
assert 'finished' in record
assert record['source_unchanged'] and record['tools_unchanged'] and not record['dependency_changes']
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()==record['provenance']['source_sha']
status=subprocess.check_output(['git','status','--porcelain'],cwd=p,text=True).splitlines()
assert not status,status
assert record['passed']
def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while chunk:=f.read(1024*1024):h.update(chunk)
 return h.hexdigest()
binaries=[]
for row in record['targets']:
 text=(run/row['log']).read_text()
 for name in re.findall(r'^\s*Running .+? \(([^\n]+)\)$',text,re.M):
  path=Path(name);path=path if path.is_absolute() else p/path;assert path.is_file()
  binaries.append(dict(target=row['target'],path=name,sha256=digest(path),bytes=path.stat().st_size))
(run/'binaries.json').write_text(json.dumps(binaries,indent=2)+'\n')
out=p/'reports/perf/2026-09-20-linux-original-module-floor';out.mkdir();artifacts=[]
def copy(src,name):
 raw=src.read_bytes();compress=src.suffix in ['.log','.patch'] or len(raw)>16000
 stored=gzip.compress(raw,mtime=0) if compress else raw;name += '.gz' if compress else ''
 dst=out/name;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(stored)
 row=dict(path=name,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
 if compress:row.update(stored_sha256=hashlib.sha256(stored).hexdigest(),stored_bytes=len(stored))
 artifacts.append(row)
for src in sorted(run.rglob('*')):
 if src.is_file():copy(src,'records/'+str(src.relative_to(run)))
for name in ['qualify-cg-module-receipt-floor-second-20260920.py','qualify-cg-module-receipt-floor-20260920.py','run-command-to-log.py','cg-module-receipt-floor-second.log','cg-module-receipt-floor-first.log','archive-cg-module-receipt-floor-20260920.py']:
 copy(r/name,'harnesses/'+name)
copy(Path('/home/ayates/ay-pblendvb-repair-20260914/scripts/_oom_guard.py'),'harnesses/_oom_guard.py')
for name in ['check_linux_aarch64.py','run_with_timeout.py','dependency_identity.py']:
 copy(p/'scripts'/name,'gate-source/'+name)
(out/'inventory.json').write_text(json.dumps(dict(artifacts=artifacts),indent=2)+'\n')
passed=sum(row['status']=='pass' for row in record['targets']);tests=sum((row.get('counts') or {}).get('passed',0) for row in record['targets'])
report=(r/'cg-module-receipt-floor-report.md').read_text().replace('@SOURCE@',record['provenance']['source_sha']).replace('@PASSED@',str(passed)).replace('@FAILED@',str(len(record['targets'])-passed)).replace('@TESTS@',str(tests)).replace('@VERDICT@','PASS' if record['passed'] else 'FAIL')
(out/'README.md').write_text(report)
subprocess.run(['python3','scripts/check_evidence_archive.py',str(out)],cwd=p,check=True)
print(json.dumps(dict(report=str(out),artifacts=len(artifacts),binaries=len(binaries),passed=passed,failed=len(record['targets'])-passed)),flush=True)

ledger=p/'docs/aarch64-completion-audit-2026-09-17.md'
text=ledger.read_text();needle='## Gap index'
assert text.count(needle)==1
note=f"**2026-09-20 original-module receipt Linux regression floor:** The [127-family run](../reports/perf/2026-09-20-linux-original-module-floor/README.md) on clean `{record['provenance']['source_sha'][:9]}` passes all {passed} required families and {tests} Rust tests, after the original-module receipt and source-frame repair. Source, dependencies and tool identities remain unchanged. This is regression evidence; native callback construction and compiler integration remain open, and no L01–L14 status changes.\n\n"
ledger.write_text(text.replace(needle,note+needle))
