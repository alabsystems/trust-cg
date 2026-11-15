from pathlib import Path
import dataclasses,hashlib,json,os,subprocess,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-abi-target-20260920');out=r/'adapter-abi-cli-fixture-first'
assert json.loads((r/'cg-adapter-target-abi-floor-first/results.json').read_text())['passed']
identity=json.loads((r/'adapter-abi-cli-fixture-source.json').read_text())
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while chunk:=f.read(1024*1024):h.update(chunk)
 return h.hexdigest()
assert sha(p/identity['test'])==identity['test_sha256']
assert sha(r/'adapter-abi-cli-fixture.rs')==identity['generator_sha256']
assert sha(r/'adapter-abi-cli-driver.c')==identity['driver_sha256']
out.mkdir();deps=p/'target/debug/deps';libraries={}
for name in ['trust_ir','serde_json']:
 candidates=list(deps.glob('lib'+name+'-*.rlib'));assert candidates
 libraries[name]=max(candidates,key=lambda path:path.stat().st_mtime_ns)
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_','RUST'))}
rustc=Path('/home/ayates/.rustup/toolchains/1.97.1-aarch64-unknown-linux-gnu/bin/rustc')
env['PATH']=str(rustc.parent)+':/usr/bin:/bin';env['RUSTUP_TOOLCHAIN']='1.97.1'
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Serialize the qualified ABI fixture for installed CLI execution')
record=dict(source=identity,resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,libraries={name:dict(path=str(path),sha256=sha(path)) for name,path in libraries.items()},rustc=dict(path=str(rustc),sha256=sha(rustc)),commands=[])
def run(label,command):
 result=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(out/(label+'.log')),*map(str,command)],16384,300,label=label,env=env,cwd=p)
 row=dataclasses.asdict(result);row.update(command=list(map(str,command)),label=label);record['commands'].append(row)
 (out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
 assert result.returncode==0 and not any([result.timed_out,result.memout,result.cancelled,result.stdout_truncated,result.stderr_truncated])
command=[rustc,'--edition=2024','--crate-name','adapter_abi_cli_fixture',r/'adapter-abi-cli-fixture.rs','-L','dependency='+str(deps),'-o',out/'generate']
for name,path in libraries.items():command+=['--extern',name+'='+str(path)]
run('build',command);run('generate',[out/'generate'])
raw=(out/'generate.log').read_bytes();module=json.loads(raw);assert len(module['functions'])==12
(out/'fixture.json').write_bytes(raw);(out/'driver.c').write_bytes((r/'adapter-abi-cli-driver.c').read_bytes())
record.update(passed=True,fixture_sha256=sha(out/'fixture.json'),driver_sha256=sha(out/'driver.c'),generator_sha256=sha(out/'generate'))
(out/'results.json').write_text(json.dumps(record,indent=2)+'\n');print('Qualified ABI fixture serialized for CLI execution',flush=True)
