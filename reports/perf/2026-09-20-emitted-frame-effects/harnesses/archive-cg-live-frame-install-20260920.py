from pathlib import Path
import gzip,hashlib,json,subprocess
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917')
installed=json.loads((r/'installed-live-frame-first/identity.json').read_text());assert len(installed['preflight'])==234 and all(x['exit_code']==0 for x in installed['preflight'])
release=json.loads((r/'cg-live-frame-release-first/result.json').read_text());assert release['passed'] and release['inputs_unchanged']
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()==release['source']
assert not subprocess.check_output(['git','status','--porcelain'],cwd=p)
assert json.loads((r/'installed-live-frame-smoke-first/results.json').read_text())['passed']
for row in installed['tools']:assert hashlib.sha256(Path(row['executable']).read_bytes()).hexdigest()==row['sha256']
assert hashlib.sha256(Path(installed['private_backend']['path']).read_bytes()).hexdigest()==installed['private_backend']['sha256']
assert hashlib.sha256(Path(installed['launcher']['path']).read_bytes()).hexdigest()==installed['launcher']['sha256']
out=p/'reports/perf/2026-09-20-live-frame-install';out.mkdir();artifacts=[]
def copy(src,name):
 raw=src.read_bytes();compress=src.suffix in ['.log','.patch','.o','.c','.S','.rs'] or len(raw)>16000 or src.suffix==''
 stored=gzip.compress(raw,mtime=0) if compress else raw;name += '.gz' if compress else ''
 dst=out/name;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(stored)
 row=dict(path=name,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
 if compress:row.update(stored_sha256=hashlib.sha256(stored).hexdigest(),stored_bytes=len(stored))
 artifacts.append(row)
for folder in ['cg-live-frame-release-first','installed-live-frame-first','installed-live-frame-smoke-first']:
 for src in sorted((r/folder).rglob('*')):
  if src.is_file() and src.suffix!='.so' and 'cache' not in src.relative_to(r/folder).parts:copy(src,'records/'+str(src.relative_to(r)))
for name in ['build-cg-live-frame-release-20260920.py','install-cg-live-frame-20260920.py','smoke-cg-live-frame-install-20260920.py','aot_arithmetic_fixture.py','select_cohort_fixture.py','diamond_cohort_fixture.py','run-command-to-log.py']:
 copy(r/name,'harnesses/'+name)
for folder in (r/'cg-live-frame-bounds-native-first').iterdir():
 if folder.is_dir():
  for name in ['runner.c','abi.S']:copy(folder/name,'rust-oracles/'+folder.name+'/'+name)
for folder in (r/'cg-live-frame-address-native-first').iterdir():
 if folder.is_dir():
  for src in folder.iterdir():
   if src.suffix in ['.c','.S']:copy(src,'rust-oracles/'+folder.name+'/'+src.name)
(out/'inventory.json').write_text(json.dumps(dict(artifacts=artifacts),indent=2)+'\n')
(out/'README.md').write_text((r/'cg-live-frame-install-report.md').read_text().replace('@SOURCE@',release['source']).replace('@DIRECTORY@',installed['directory']).replace('@CLI_SHA@',release['sha256']).replace('@BACKEND_SHA@',installed['private_backend']['sha256']).replace('@SECONDS@',f"{release['seconds']:.2f}"))
subprocess.run(['python3','scripts/check_evidence_archive.py',str(out)],cwd=p,check=True)
print(json.dumps(dict(report=str(out),artifacts=len(artifacts))),flush=True)
