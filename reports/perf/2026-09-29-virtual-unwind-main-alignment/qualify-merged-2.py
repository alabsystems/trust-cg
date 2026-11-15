from pathlib import Path
import subprocess,json,shutil,hashlib
p=Path('$HOME/trust-cg/target/virtual-unwind-investigation');root=p.parents[1]
cmd=['python3',str(root/'target/pointer-bytes-investigation/workspace-build.py'),'test','-p','trust-cg-opt','--lib','--no-run','--message-format=json']
with (p/'opt-build-merged-2.log').open('wb') as log:r=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=900)
assert r.returncode==0,r.returncode
es=[]
for line in (p/'opt-build-merged-2.log').read_text().splitlines():
 try:es.append(json.loads(line))
 except ValueError:pass
a=[x for x in es if x.get('reason')=='compiler-artifact' and x.get('target',{}).get('name')=='trust_cg_opt' and x.get('executable')];assert len(a)==1
src=Path(a[0]['executable']);dst=p/'opt-merged-2.test';shutil.copy2(src,dst)
(p/'opt-build-merged-2-receipt.json').write_text(json.dumps(dict(command=cmd,original_path=str(src),immutable_path=str(dst),sha256=hashlib.sha256(dst.read_bytes()).hexdigest()),indent=2)+'\n');print('opt built',flush=True)
exec((p/'env.py').read_text());env['XDG_CACHE_HOME']='/tmp/trust-cg-borrowed-aggregate-proof-qjyzzw76'
cmd=[str(dst),'x86_peephole::tests::','--nocapture','--test-threads=1']
with (p/'opt-merged-2.log').open('wb') as log:r=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=300)
(p/'opt-merged-2-results.json').write_text(json.dumps(dict(command=cmd,returncode=r.returncode,sha256=hashlib.sha256(dst.read_bytes()).hexdigest()),indent=2)+'\n');print('opt tests',r.returncode,flush=True)
raise SystemExit(r.returncode)
