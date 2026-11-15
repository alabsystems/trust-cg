from pathlib import Path
import gzip,hashlib,json,re,subprocess
r=Path('/home/ayates/trust-cg-soundness-20260914');b=Path('/home/ayates/trust-cg-output-byte-binding-20260917')
for run,expected in [('bytes-final-integration',[5,8,5]),('bytes-final-frame',[67])]:
 record=json.loads((r/('cg-cell-source-'+run)/'result.json').read_text());assert record['complete'] and record['passed'] and record['source_unchanged']
 log=(r/('cg-cell-source-'+run)/'command.log').read_text();counts=[int(x) for x in re.findall(r'test result: ok\. (\d+) passed; 0 failed; 0 ignored;',log)];assert counts==expected,(run,counts)
assert 'check_fmt: OK' in (r/'cg-cell-bytes-fmt-second.log').read_text()
assert 'OK (skipped=1)' in (r/'cg-cell-bytes-linux-gate-tests.log').read_text()
out=b/'reports/perf/2026-09-20-scalar-cell-elf-binding';out.mkdir();artifacts=[]
def add(raw,name,compress=False):
 compress=compress or len(raw)>16000;stored=gzip.compress(raw,mtime=0) if compress else raw
 if compress:name+='.gz'
 dst=out/name;assert not dst.exists();dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(stored)
 row=dict(path=name,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
 if compress:row.update(stored_sha256=hashlib.sha256(stored).hexdigest(),stored_bytes=len(stored))
 artifacts.append(row)
def copy(src,name):add(src.read_bytes(),name,src.suffix in ['.log','.patch'])
for run in ['bytes-first','bytes-second','bytes-third','bytes-fourth','bytes-frame','bytes-final-integration','bytes-final-frame']:
 for src in sorted((r/('cg-cell-source-'+run)).rglob('*')):
  if src.is_file():copy(src,'records/'+str(src.relative_to(r)))
counts={key:0 for key in ['CELL_BYTES','CELL_ELF','CELL_GNU_OBJECT']}
log=(r/'cg-cell-source-bytes-final-integration/command.log').read_text()
for line in log.splitlines():
 for kind in counts:
  if kind+' {' not in line:continue
  row=json.loads(line.split(kind+' ',1)[1]);counts[kind]+=1
  if kind=='CELL_BYTES':
   add(bytes(row['code']),'objects/pipeline/'+row['case']+'.bin')
   add((json.dumps({k:v for k,v in row.items() if k!='code'},indent=2)+'\n').encode(),'objects/pipeline/'+row['case']+'.call.json')
  elif kind=='CELL_ELF':add(bytes(row['object']),'objects/pipeline/'+row['case']+'.o')
  else:
   name=row['case']+('-movn' if row['movn'] else '-movz')
   add(bytes(row['object']),'objects/gnu/'+name+'.o');add(row['assembly'].encode(),'objects/gnu/'+name+'.s')
assert counts=={'CELL_BYTES':24,'CELL_ELF':24,'CELL_GNU_OBJECT':6},counts
for name in ['cg-cell-bytes-fmt.log','cg-cell-bytes-fmt-second.log','cg-cell-bytes-linux-gate-tests.log']:
 copy(r/name,'records/'+name)
for name in ['run-cg-cell-check-20260920.py','run-command-to-log.py','qualify-cg-cell-bytes-final-20260920.py','archive-cg-cell-bytes-20260920.py']:
 copy(r/name,'harnesses/'+name)
copy(Path('/home/ayates/ay-pblendvb-repair-20260914/scripts/_oom_guard.py'),'harnesses/_oom_guard.py')
for src in [b/'crates/trust-cg-verify/src/source_bound_frame.rs',b/'crates/trust-cg-verify/tests/aarch64_scalar_cell_bytes.rs',b/'scripts/check_linux_aarch64.py',b/'scripts/tests/test_linux_aarch64_gate.py',*sorted((b/'crates/trust-cg-verify/src').glob('source_bound_cell*'))]:
 if src.suffix in ['.rs','.json','.py']:copy(src,'source/'+str(src.relative_to(b)))
(out/'inventory.json').write_text(json.dumps(dict(artifacts=artifacts),indent=2)+'\n')
(out/'README.md').write_text((r/'cg-cell-bytes-report.md').read_text())
subprocess.run(['python3','scripts/check_evidence_archive.py',str(out)],cwd=b,check=True)
print(json.dumps(dict(artifacts=len(artifacts),objects=counts,directory=str(out))))
