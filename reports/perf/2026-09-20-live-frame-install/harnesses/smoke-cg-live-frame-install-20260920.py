from pathlib import Path
import hashlib,json,os,subprocess,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917');out=r/'installed-live-frame-smoke-first';out.mkdir()
identity=json.loads((r/'installed-live-frame-first/identity.json').read_text());package=Path(identity['directory']);sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(Path(identity['launcher']['path']))==identity['launcher']['sha256']
for tool in identity['tools']:assert sha(Path(tool['executable']))==tool['sha256']
for name in ['ay','clean']:assert (Path('/home/ayates/.local/bin')/name).resolve()==package/name
assert sha(Path(identity['private_backend']['path']))==identity['private_backend']['sha256']
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Activated compiler launcher smoke')
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_'))};env['PATH']='/home/ayates/.local/bin:/usr/bin:/bin'
commands=[('version',['/home/ayates/.local/bin/trust-cg','--version']),('compile',['/home/ayates/.local/bin/trust-cg','--format=text','--target','aarch64-unknown-linux-gnu','-O3','-c','examples/return_42.trust_ir','--emit-proofs',str(out/'proofs'),'-o',str(out/'return42.o')]),('link',['cc','examples/return_42.c',str(out/'return42.o'),'-o',str(out/'return42')]),('run',[str(out/'return42')])]
rows=[]
for name,cmd in commands:
 result=guard.run_captured(cmd,16384,120,label=name,env=env,cwd=p);(out/(name+'.log')).write_text(result.stdout+result.stderr)
 assert not(result.returncode or result.memout or result.timed_out or result.cancelled or result.stdout_truncated or result.stderr_truncated)
 if name=='run':assert result.stdout.strip()=='42'
 rows.append(dict(command=cmd,exit_code=result.returncode,seconds=result.wall_sec,guard_evidence=result.guard_evidence))
(out/'results.json').write_text(json.dumps(dict(passed=True,installed=identity['directory'],resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,checks=rows),indent=2)+'\n')
print('Activated launcher and all tool identities PASS; proof export/link/run PASS')
