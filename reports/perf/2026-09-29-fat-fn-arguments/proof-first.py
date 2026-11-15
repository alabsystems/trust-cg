from pathlib import Path
import subprocess,json,time,hashlib
p=Path('$HOME/trust-cg/target/fat-fn-spread-investigation');exec((p/'env.py').read_text());env['XDG_CACHE_HOME']='/tmp/trust-cg-borrowed-aggregate-proof-qjyzzw76'
source=p/'proof-first-source.rs';source.write_bytes(Path('$HOME/trust-cg/crates/rustc-codegen-trust-cg/tests/support/residual_conversion/fat_fn_arguments.rs').read_bytes());rows=[]
for mode in ['strict','machine']:
 for opt in [0,2]:
  d=p/f'proof-first-{mode}-O{opt}';d.mkdir(exist_ok=True)
  args='diag-json refine refine-trace bridge-coverage-strict=1'+(' no-proof-certs' if mode=='strict' else '')
  cmd=[str(tc/'bin/trustc'),'--edition=2024','--crate-type=lib','--emit=obj,mir','-Cpanic=unwind','-Crelocation-model=pic',f'-Copt-level={opt}','-Ccodegen-units=1','-Ztrust-verify=off',str(source),'--out-dir',str(d),'-Zcodegen-backend='+str(p/'first-backend.so'),'-Ztrust-ir-cg-args='+args]
  start=time.monotonic()
  with (d/'compile.log').open('wb') as log:r=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=180)
  rows.append(dict(mode=mode,opt=opt,command=cmd,returncode=r.returncode,wall_seconds=time.monotonic()-start,backend_sha256=hashlib.sha256((p/'first-backend.so').read_bytes()).hexdigest()));(p/'proof-first-results.json').write_text(json.dumps(rows,indent=2)+'\n');print(mode,opt,r.returncode,flush=True)
