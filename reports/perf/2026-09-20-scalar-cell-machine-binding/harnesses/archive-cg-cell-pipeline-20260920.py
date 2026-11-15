from pathlib import Path
import gzip,hashlib,json,re,subprocess
r=Path('/home/ayates/trust-cg-soundness-20260914');b=Path('/home/ayates/trust-cg-output-byte-binding-20260917')
for run,expected in [('pipeline-fifth',[67]),('pipeline-integration-second',[8,5])]:
 record=json.loads((r/('cg-cell-source-'+run)/'result.json').read_text());assert record['complete'] and record['passed'] and record['source_unchanged']
 log=(r/('cg-cell-source-'+run)/'command.log').read_text();counts=[int(x) for x in re.findall(r'test result: ok\. (\d+) passed; 0 failed; 0 ignored;',log)];assert counts==expected,(run,counts)
assert 'check_fmt: OK' in (r/'cg-cell-pipeline-fmt.log').read_text()
out=b/'reports/perf/2026-09-20-scalar-cell-machine-binding';out.mkdir();artifacts=[]
def copy(src,name):
 raw=src.read_bytes();compressed=len(raw)>16000 or src.suffix in ['.log','.patch'];stored=gzip.compress(raw,mtime=0) if compressed else raw
 if compressed:name+='.gz'
 dst=out/name;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(stored)
 row=dict(path=name,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
 if compressed:row.update(stored_sha256=hashlib.sha256(stored).hexdigest(),stored_bytes=len(stored))
 artifacts.append(row)
for run in ['pipeline-first','pipeline-second','pipeline-third','pipeline-diagnose','pipeline-fourth','pipeline-fifth','pipeline-integration','pipeline-integration-second']:
 for src in sorted((r/('cg-cell-source-'+run)).rglob('*')):
  if src.is_file():copy(src,'records/'+str(src.relative_to(r)))
for identity in json.loads((r/'cg-cell-machine-identities.json').read_text()):
 src=r/'cg-call-frame-capture-repaired'/(identity['case']+'.frame-inputs.json');assert hashlib.sha256(src.read_bytes()).hexdigest()==identity['capture_sha256'];copy(src,'captures/'+src.name)
for name in ['cg-cell-pipeline-fmt.log','cg-cell-machine-identities.json']:
 copy(r/name,'records/'+name)
for name in ['run-cg-cell-check-20260920.py','generate-cg-cell-machine-identities-20260920.py','run-command-to-log.py','archive-cg-cell-pipeline-20260920.py']:
 copy(r/name,'harnesses/'+name)
copy(Path('/home/ayates/ay-pblendvb-repair-20260914/scripts/_oom_guard.py'),'harnesses/_oom_guard.py')
for src in [b/'crates/trust-cg-verify/src/source_bound_frame.rs',b/'crates/trust-cg-verify/src/source_bound_output_memory.rs',*sorted((b/'crates/trust-cg-verify/src').glob('source_bound_cell*'))]:
 if src.suffix in ['.rs','.json']:copy(src,'source/'+str(src.relative_to(b)))
(out/'inventory.json').write_text(json.dumps(dict(artifacts=artifacts),indent=2)+'\n')
(out/'README.md').write_text((r/'cg-cell-pipeline-report.md').read_text())
subprocess.run(['python3','scripts/check_evidence_archive.py',str(out)],cwd=b,check=True)
print(json.dumps(dict(artifacts=len(artifacts),directory=str(out))))
