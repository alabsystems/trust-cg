from pathlib import Path
import subprocess, json, shutil, hashlib, time
p=Path('$HOME/trust-cg/target/slice-from-end-investigation');root=p.parents[1]
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
cmd=['python3',str(root/'target/main-alignment-20260929/build-online.py'),'test','--lib','--no-run','--message-format=json']
with (p/'bridge-unit-alignment-build.log').open('wb') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=1800)
assert r.returncode==0,r.returncode
events=[]
for line in (p/'bridge-unit-alignment-build.log').read_text().splitlines():
    try:events.append(json.loads(line))
    except ValueError:pass
assert any(e.get('reason')=='build-finished' and e['success'] for e in events)
a=[e for e in events if e.get('reason')=='compiler-artifact' and e.get('target',{}).get('name')=='rustc_codegen_trust_cg' and e.get('executable')]
assert len(a)==1
src=Path(a[0]['executable']);dst=p/'bridge-unit-alignment.test';shutil.copy2(src,dst)
receipt=dict(command=cmd,source_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),original_path=str(src),immutable_path=str(dst),sha256=sha(dst))
(p/'bridge-unit-alignment-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
exec((p/'env.py').read_text());env['XDG_CACHE_HOME']='/tmp/trust-cg-borrowed-aggregate-proof-qjyzzw76'
cmd=[str(dst),'knobs::tests::','--nocapture','--test-threads=1'];start=time.monotonic()
with (p/'bridge-unit-alignment.log').open('wb') as f:r=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=300)
(p/'bridge-unit-alignment-results.json').write_text(json.dumps(dict(command=cmd,returncode=r.returncode,wall_seconds=time.monotonic()-start,sha256=sha(dst)),indent=2)+'\n')
print('knobs',r.returncode,flush=True);raise SystemExit(r.returncode)
