from pathlib import Path
import dataclasses,hashlib,json,os,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917');out=r/'cg-live-frame-previous-backend-first';out.mkdir()
old=json.loads((r/'installed-direct-branch-first/identity.json').read_text());backend=Path(old['private_backend']['path']);assert hashlib.sha256(backend.read_bytes()).hexdigest()==old['private_backend']['sha256']
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Previous backend masked-index unwind baseline')
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_'))};env.update(PATH=str(Path(old['directory'])/'bin')+':/usr/bin:/bin',XDG_CACHE_HOME=str(out/'cache'))
source=r/'cg-live-frame-production-first/bounds_unwind.rs';assert source.exists();record=dict(scope='Old installed backend on the exact new-qualification Rust input and path. Frontend explicitly unverified, backend checks enabled.',backend=old['private_backend']['sha256'],source=str(source),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,cases=[])
for level in [2,3]:
 folder=out/f'O{level}';folder.mkdir();cmd=['/home/ayates/toolchains/trust-a62ae50d/bin/trustc','--edition=2024','--crate-type=lib','--emit=obj','-Cpanic=unwind','--target','aarch64-unknown-linux-gnu',f'-Copt-level={level}','-Ztrust-verify=off','-Zcodegen-backend='+str(backend),str(source),'-o',str(folder/'bounds_unwind.o')]
 result=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(out/f'O{level}.log'),*cmd],16384,300,label=f'O{level}',env=env,cwd=p)
 record['cases'].append(dict(level=level,command=cmd,**dataclasses.asdict(result)));(out/'results.json').write_text(json.dumps(record,indent=2)+'\n');assert not any([result.memout,result.timed_out,result.cancelled,result.stdout_truncated,result.stderr_truncated])
record['complete']=True;(out/'results.json').write_text(json.dumps(record,indent=2)+'\n');print([(c['level'],c['returncode']) for c in record['cases']],flush=True)
