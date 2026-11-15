from pathlib import Path
import subprocess,json,hashlib,time
p=Path('$HOME/trust-cg/target/fat-fn-spread-investigation');exec((p/'env.py').read_text());b=p/'merged-backend.so'
env.update(TCG_TEST_BACKEND_PATH=str(b),TCG_TEST_BACKEND_SHA256=hashlib.sha256(b.read_bytes()).hexdigest(),XDG_CACHE_HOME='/tmp/trust-cg-borrowed-aggregate-proof-qjyzzw76',TMPDIR=str(p))
cmd=[str(p/'overflow-merged-2.test'),'--nocapture','--test-threads=1'];start=time.monotonic()
with (p/'overflow-baseline.log').open('wb') as log:r=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=300)
(p/'overflow-baseline-results.json').write_text(json.dumps(dict(command=cmd,returncode=r.returncode,wall_seconds=time.monotonic()-start,backend_sha256=env['TCG_TEST_BACKEND_SHA256']),indent=2)+'\n');print('overflow baseline',r.returncode,flush=True)
