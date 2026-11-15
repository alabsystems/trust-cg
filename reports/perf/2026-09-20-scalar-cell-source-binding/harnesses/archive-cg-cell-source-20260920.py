from pathlib import Path
import gzip,hashlib,json,subprocess
r=Path('/home/ayates/trust-cg-soundness-20260914');b=Path('/home/ayates/trust-cg-output-byte-binding-20260917')
for run in ['second','integration']:
    rec=json.loads((r/('cg-cell-source-'+run)/'result.json').read_text())
    assert rec['complete'] and rec['passed'] and rec['source_unchanged']
assert '60 passed; 0 failed' in (r/'cg-cell-source-second/command.log').read_text()
assert '8 passed; 0 failed' in (r/'cg-cell-source-integration/command.log').read_text()
assert '5 passed; 0 failed' in (r/'cg-cell-source-integration/command.log').read_text()
assert 'check_fmt: OK' in (r/'cg-cell-source-fmt.log').read_text()
assert 'OK (skipped=1)' in (r/'cg-cell-source-linux-gate-tests-second.log').read_text()
out=b/'reports/perf/2026-09-20-scalar-cell-source-binding';out.mkdir()
artifacts=[]
def copy(src,name):
    raw=src.read_bytes();compressed=len(raw)>16000 or src.suffix in ['.log','.patch']
    stored=gzip.compress(raw,mtime=0) if compressed else raw
    if compressed:name+='.gz'
    dst=out/name;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(stored)
    row=dict(path=name,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
    if compressed:row.update(stored_sha256=hashlib.sha256(stored).hexdigest(),stored_bytes=len(stored))
    artifacts.append(row)
for run in ['cg-call-frame-capture-first','cg-call-frame-capture-repaired','cg-cell-source-first','cg-cell-source-second','cg-cell-source-integration']:
    for src in sorted((r/run).rglob('*')):
        if src.is_file() and src.suffix!='.so' and 'cache' not in src.relative_to(r/run).parts:
            copy(src,'records/'+str(src.relative_to(r)))
for name in ['cg-call-frame-instrumentation.json','cg-call-frame-instrumentation.patch','cg-call-frame-capture-restored.json','cg-call-frame-repaired-instrumentation.json','cg-call-frame-repaired-instrumentation.patch','cg-call-frame-repaired-capture-restored.json','cg-cell-source-fmt.log','cg-cell-source-linux-gate-tests.log','cg-cell-source-linux-gate-tests-second.log']:
    copy(r/name,'records/'+name)
for name in ['prepare-cg-call-frame-capture-20260920.py','capture-cg-call-frame-20260920.py','restore-cg-call-frame-capture-20260920.py','prepare-cg-cell-pointer-recapture-20260920.py','capture-cg-cell-pointer-repair-20260920.py','restore-cg-cell-pointer-recapture-20260920.py','run-cg-cell-check-20260920.py','generate-cg-cell-source-fixtures-20260920.py','run-command-to-log.py','archive-cg-cell-source-20260920.py']:
    copy(r/name,'harnesses/'+name)
copy(Path('/home/ayates/ay-pblendvb-repair-20260914/scripts/_oom_guard.py'),'harnesses/_oom_guard.py')
for src in [b/'crates/rustc-codegen-trust-cg/src/canonicalize_copies.rs',b/'crates/trust-cg-verify/tests/bridge_copy_types.rs',*sorted((b/'crates/trust-cg-verify/src').glob('source_bound_cell*'))]:
    if src.suffix in ['.rs','.json']:copy(src,'source/'+str(src.relative_to(b)))
(out/'inventory.json').write_text(json.dumps(dict(artifacts=artifacts),indent=2)+'\n')
(out/'README.md').write_text((r/'cg-cell-source-report.md').read_text())
subprocess.run(['python3','scripts/check_evidence_archive.py',str(out)],cwd=b,check=True)
print(json.dumps(dict(artifacts=len(artifacts),directory=str(out))))
