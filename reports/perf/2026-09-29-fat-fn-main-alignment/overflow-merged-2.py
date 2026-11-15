from pathlib import Path
import subprocess,json,shutil,hashlib,time
root=Path('$HOME/trust-cg');p=root/'target/fat-fn-spread-investigation'
cmd=['python3',str(root/'target/main-alignment-20260929/build-online.py'),'test','--test','overflow_asserts','--no-run','--message-format=json']
with (p/'overflow-build-merged-2.log').open('wb') as log:r=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=1200)
assert r.returncode==0,r.returncode
es=[]
for line in (p/'overflow-build-merged-2.log').read_text().splitlines():
 try:es.append(json.loads(line))
 except ValueError:pass
assert any(e.get('reason')=='build-finished' and e['success'] for e in es)
a=[e for e in es if e.get('reason')=='compiler-artifact' and e.get('target',{}).get('name')=='overflow_asserts' and e.get('executable')];assert len(a)==1
src=Path(a[0]['executable']);dst=p/'overflow-merged-2.test';shutil.copy2(src,dst)
(p/'overflow-build-merged-2-receipt.json').write_text(json.dumps(dict(command=cmd,original_path=str(src),immutable_path=str(dst),sha256=hashlib.sha256(dst.read_bytes()).hexdigest()),indent=2)+'\n')
exec((p/'env.py').read_text());b=p/'merged-2-backend.so'
env.update(TCG_TEST_BACKEND_PATH=str(b),TCG_TEST_BACKEND_SHA256=hashlib.sha256(b.read_bytes()).hexdigest(),XDG_CACHE_HOME='/tmp/trust-cg-borrowed-aggregate-proof-qjyzzw76',TMPDIR=str(p))
cmd=[str(dst),'--nocapture','--test-threads=1'];start=time.monotonic()
with (p/'overflow-merged-2.log').open('wb') as log:r=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=300)
(p/'overflow-merged-2-results.json').write_text(json.dumps(dict(command=cmd,returncode=r.returncode,wall_seconds=time.monotonic()-start,backend_sha256=env['TCG_TEST_BACKEND_SHA256']),indent=2)+'\n');print('overflow tests',r.returncode,flush=True)
raise SystemExit(r.returncode)
