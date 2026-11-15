from pathlib import Path
import subprocess,json,hashlib,time,shutil
p=Path('$HOME/trust-cg/target/fat-fn-spread-investigation');exec((p/'env.py').read_text())
env.update(XDG_CACHE_HOME='/tmp/trust-cg-borrowed-aggregate-proof-qjyzzw76',TMPDIR=str(p))
rows=[]
for label,b in [('before',p/'merged-backend.so'),('after',p/'merged-2-backend.so')]:
 d=p/f'overflow-{label}'/'deps';d.mkdir(parents=True,exist_ok=True)
 test=d/'overflow_asserts';library=d/'librustc_codegen_trust_cg.so'
 shutil.copy2(p/'overflow-merged-2.test',test);shutil.copy2(b,library)
 cmd=[str(test),'--nocapture','--test-threads=1'];start=time.monotonic()
 with (p/f'overflow-comparison-{label}.log').open('wb') as log:r=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=300)
 rows.append(dict(label=label,command=cmd,returncode=r.returncode,wall_seconds=time.monotonic()-start,backend_sha256=hashlib.sha256(library.read_bytes()).hexdigest(),test_sha256=hashlib.sha256(test.read_bytes()).hexdigest()))
 (p/'overflow-comparison-results.json').write_text(json.dumps(rows,indent=2)+'\n');print(label,r.returncode,flush=True)
