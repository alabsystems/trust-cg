from pathlib import Path
import gzip, hashlib, json, subprocess
r=Path('/home/ayates/trust-cg-soundness-20260914')
p=Path('/home/ayates/trust-cg-output-byte-binding-20260917')
report=json.loads((r/'cg-core-byte-writer-frame-sixth/gate/report.json').read_text())
assert report['passed']
assert len(report['rejections'])==44 and len(report['acceptances'])==11
assert report['execution']['counts']==dict(passed=9,failed=0,ignored=0,measured=0,filtered=0)
request=json.loads((r/'cg-core-byte-writer-frame-sixth/gate.request.json').read_text())
for name,sha in request['inputs'].items():
 assert hashlib.sha256((p/name).read_bytes()).hexdigest()==sha,name
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()==request['head']
out=p/'reports/perf/2026-09-20-core-byte-writer-frame'
out.mkdir()
artifacts=[]
def copy(src,name):
 raw=src.read_bytes()
 compressed=src.suffix in ('.log','.patch','.dag','.rejected-dag') or len(raw)>16000
 stored=gzip.compress(raw,mtime=0) if compressed else raw
 name += '.gz' if compressed else ''
 dst=out/name;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(stored)
 row=dict(path=name,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
 if compressed:row.update(stored_sha256=hashlib.sha256(stored).hexdigest(),stored_bytes=len(stored))
 artifacts.append(row)
for attempt in ['first','second','third','fourth','fifth','sixth']:
 folder=r/('cg-core-byte-writer-frame-'+attempt)
 for src in sorted(folder.rglob('*')):
  if src.is_file():copy(src,'records/'+str(src.relative_to(r)))
for name in ['qualify-cg-core-byte-writer-frame-20260920.py','qualify-cg-core-byte-writer-frame-gate-20260920.py','archive-cg-core-byte-writer-frame-20260920.py']:
 copy(r/name,'harnesses/'+name)
for name in ['crates/trust-cg-verify/tests/core_byte_writer.rs','crates/trust-cg-verify/tests/core_byte_writer/symbolic.rs','crates/trust-cg-verify/tests/core_byte_writer/caller.rs','crates/trust-cg-verify/tests/core_byte_writer/retirement.rs','crates/trust-cg-verify/tests/core_byte_writer/private_frame.rs','scripts/check_core_byte_writer.py','crates/trust-cg-verify/tests/fixtures/output_memory_writer-layout-O1.trust-ir.json']:
 copy(p/name,'source/'+name)
patch=r/'cg-core-byte-writer-frame-candidate.patch'
patch.write_bytes(subprocess.check_output(['git','diff','--binary','HEAD'],cwd=p))
copy(patch,'source/candidate.patch')
(out/'inventory.json').write_text(json.dumps(dict(artifacts=artifacts),indent=2)+'\n')
execution=report['execution']
draft=(r/'cg-core-byte-writer-frame-report-draft.md').read_text()
draft=draft.replace('GATE_SECONDS',f"{execution['elapsed_seconds']:.2f}").replace('GATE_RSS_MIB',str(execution['rss']['sampled_peak_mib']))
(out/'README.md').write_text(draft)
subprocess.run(['python3','scripts/check_evidence_archive.py',str(out)],cwd=p,check=True)
print(json.dumps(dict(report=str(out),artifacts=len(artifacts),stored_bytes=sum(a.get('stored_bytes',a['bytes']) for a in artifacts))),flush=True)
