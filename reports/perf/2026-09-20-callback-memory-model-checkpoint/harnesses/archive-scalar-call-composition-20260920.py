from pathlib import Path
import gzip,hashlib,json,subprocess
r=Path('/home/ayates/trust-cg-soundness-20260914');b=Path('/home/ayates/trust-cg-output-byte-binding-20260917')
records={key:json.loads((r/('scalar-call-composition-replay-'+key)/'results.json').read_text()) for key in ['first','normalized','diagnose','claims']}
assert all(x['complete'] and not x['passed'] for x in records.values())
assert sum(x['answers']==['sat'] for x in records['first']['cases'])==13
assert sum(x['answers']==['sat'] for x in records['normalized']['cases'])==20
assert all(x['answers']==['unknown'] for x in records['diagnose']['cases'])
assert sum(x['replayed'] for x in records['claims']['cases'])==2
assert sum(sum(c['rejected'] for c in x['controls']) for x in records['claims']['cases'])==6
for rec in records.values():
    assert all(not any(cmd[k] for k in ['timed_out','memout','cancelled','stdout_truncated','stderr_truncated']) for cmd in rec['commands'])
out=b/'reports/perf/2026-09-20-callback-memory-model-checkpoint';out.mkdir()
artifacts=[]
def copy(src,name):
    raw=src.read_bytes();compressed=len(raw)>16000 or src.suffix=='.log';stored=gzip.compress(raw,mtime=0) if compressed else raw
    if compressed:name+='.gz'
    dst=out/name;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(stored)
    row=dict(path=name,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
    if compressed:row.update(stored_sha256=hashlib.sha256(stored).hexdigest(),stored_bytes=len(stored))
    artifacts.append(row)
for folder in ['scalar-call-composition-prototype-second','scalar-call-composition-prototype-normalized','scalar-call-composition-claims',*[f'scalar-call-composition-replay-{x}' for x in records]]:
    for src in sorted((r/folder).rglob('*')):
        if src.is_file():copy(src,'records/'+str(src.relative_to(r)))
for src in sorted(r.glob('scalar-call-composition-probe-*.log')):copy(src,'records/'+src.name)
for name in ['generate-scalar-call-composition-second-20260920.py','generate-scalar-call-composition-normalized-20260920.py','probe-scalar-call-composition-20260920.py','probe-scalar-call-composition-normalized-20260920.py','probe-scalar-call-composition-diagnose-20260920.py','isolate-scalar-call-claims-20260920.py','probe-scalar-call-claims-20260920.py','run-command-to-log.py','archive-scalar-call-composition-20260920.py']:
    copy(r/name,'harnesses/'+name)
copy(Path('/home/ayates/ay-pblendvb-repair-20260914/scripts/_oom_guard.py'),'harnesses/_oom_guard.py')
copy(r/'ay-at-tree-43f133d3/identity.json','solver-source/binary-build-identity.json')
ay=Path('/home/ayates/ay-output-memory-repair-20260917')
for name in ['arrays.rs','words.rs','lower.rs']:
    path='crates/ay-proof/src/alethe_printer/bv_packed/circuit/'+name
    data=subprocess.check_output(['git','show','43f133d35b620b01320cc3e2d05117a82c393b1c:'+path],cwd=ay)
    local=r/('scalar-call-pinned-'+name);local.write_bytes(data);copy(local,'solver-source/'+name)
(out/'inventory.json').write_text(json.dumps(dict(artifacts=artifacts),indent=2)+'\n')
(out/'README.md').write_text((r/'scalar-call-composition-report.md').read_text())
subprocess.run(['python3','scripts/check_evidence_archive.py',str(out)],cwd=b,check=True)
print(json.dumps(dict(directory=str(out),artifacts=len(artifacts))))
