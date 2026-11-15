from pathlib import Path
import hashlib,json
r=Path('/home/ayates/trust-cg-soundness-20260914')
b=Path('/home/ayates/trust-cg-output-byte-binding-20260917')
rows=[]
for case in json.loads((b/'crates/trust-cg-verify/src/source_bound_cell_sources.json').read_text()):
 name=case['case'];path=r/'cg-call-frame-capture-repaired'/(name+'.frame-inputs.json');raw=path.read_bytes();capture=json.loads(raw);assert len(capture)==1
 assert capture[0]['lir']==case['lir']
 prefix=capture[0]['machine_debug'].split('    eh_metadata:')[0]
 assert prefix.endswith('    ],\n') and '    stack_slots:' in prefix
 rows.append(dict(case=name,capture_sha256=hashlib.sha256(raw).hexdigest(),machine_prefix_bytes=len(prefix.encode()),machine_prefix_sha256=hashlib.sha256(prefix.encode()).hexdigest()))
out=r/'cg-cell-machine-identities.json';out.write_text(json.dumps(rows,indent=2)+'\n');print(len(rows),out)
