from pathlib import Path
import subprocess,json,shutil,hashlib
root=Path('$HOME/trust-cg');p=root/'target/indirect-unwind-investigation'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
shutil.copy2(root/'crates/rustc-codegen-trust-cg/src/lib.rs',p/'first-lib.rs')
(p/'first-source.patch').write_bytes(subprocess.check_output(['git','diff','HEAD']))
(p/'first-source-head.txt').write_bytes(subprocess.check_output(['git','rev-parse','HEAD']))
cmd=['python3',str(root/'target/main-alignment-20260929/build-online.py'),'build','--lib','--message-format=json']
with (p/'build-first.log').open('wb') as log:r=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=900)
assert r.returncode==0,r.returncode
es=[]
for line in (p/'build-first.log').read_text().splitlines():
 try:es.append(json.loads(line))
 except ValueError:pass
assert any(e.get('reason')=='build-finished' and e['success'] for e in es)
a=[e for e in es if e.get('reason')=='compiler-artifact' and e.get('target',{}).get('name')=='rustc_codegen_trust_cg'];assert len(a)==1
src=Path(a[0]['filenames'][0]);shutil.copy2(src,p/'first-backend.so')
row=dict(command=cmd,original_path=str(src),immutable_path=str(p/'first-backend.so'),sha256=sha(p/'first-backend.so'))
(p/'build-first-receipt.json').write_text(json.dumps(row,indent=2)+'\n');print(row)
