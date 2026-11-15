from pathlib import Path
import hashlib,json
r=Path('/home/ayates/trust-cg-soundness-20260914')
b=Path('/home/ayates/trust-cg-output-byte-binding-20260917/crates/trust-cg-verify/src')
for run, suffix in [('first','_before'),('repaired','')]:
    root=r/('cg-call-frame-capture-'+run)
    record=json.loads((root/'results.json').read_text())
    assert record['complete'] and len(record['cases'])==24
    assert all(c['source_captured'] and c['frame_captures']==1 and c['proof_refusal'] and not c['objects'] and not c['diagnostic_admitted'] for c in record['cases'])
    rows=[]
    for p in sorted(root.glob('*.trust-ir.json')):
        case=p.name.removesuffix('.trust-ir.json');frames=root/(case+'.frame-inputs.json')
        frame=json.loads(frames.read_text());assert len(frame)==1
        rows.append(dict(case=case,module=json.loads(p.read_text()),lir=frame[0]['lir'],capture_sha256={'module':hashlib.sha256(p.read_bytes()).hexdigest(),'frame_inputs':hashlib.sha256(frames.read_bytes()).hexdigest()}))
    raw=(json.dumps(rows,indent=2)+'\n').encode()
    fixture=b/('source_bound_cell_sources'+suffix+'.json')
    assert fixture.read_bytes()==raw, fixture
    print(json.dumps(dict(fixture=fixture.name,sha256=hashlib.sha256(raw).hexdigest(),cases=len(rows))))
