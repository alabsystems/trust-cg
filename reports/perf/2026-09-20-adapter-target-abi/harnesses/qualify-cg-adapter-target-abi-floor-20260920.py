from pathlib import Path
import dataclasses,hashlib,importlib.util,json,os,shutil,subprocess,sys
from datetime import datetime,timezone
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-abi-target-20260920');out=r/'cg-adapter-target-abi-floor-first';out.mkdir()
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Explicit adapter target ABI Linux AArch64 regression inventory')
installed=json.loads((r/'installed-floor-repair-first/identity.json').read_text())
for key in list(os.environ):
 if key.startswith(('TCG_','TRUST_CG_','AY_')) or key in ['RUSTFLAGS','RUSTC','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_TARGET','CARGO_BUILD_RUSTC','CARGO_BUILD_RUSTC_WRAPPER','CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER']:os.environ.pop(key)
os.environ.update(PATH='/home/ayates/.rustup/toolchains/1.97.1-aarch64-unknown-linux-gnu/bin:'+installed['directory']+'/bin:/home/ayates/.cargo/bin:/home/ayates/.local/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='1.97.1',CARGO_BUILD_JOBS='2',RUST_TEST_THREADS='1',RUST_MIN_STACK='16777216',CARGO_TARGET_DIR='/home/ayates/trust-cg-abi-target-20260920/target')
os.chdir(p)
spec=importlib.util.spec_from_file_location('linux_floor',p/'scripts/check_linux_aarch64.py');gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
provenance=gate.preflight();assert not provenance['dirty'];assert len(gate.TARGETS)==129
assert provenance['source_sha']==sys.argv[1]
deps=gate.dependency_identity(provenance['tools']['git']);assert not gate.dependency_recorder().offline_problems(deps)
def tool_observations():
 rows=[]
 for name in ['cargo','rustc','cc','c++','readelf','llvm-dwarfdump','llvm-readelf','llvm-objdump','ay','clean']:
  executable=Path(shutil.which(name)).resolve();rows.append(dict(name=name,path=str(executable),sha256=hashlib.sha256(executable.read_bytes()).hexdigest(),bytes=executable.stat().st_size))
 return rows
record=dict(scope='All 129 required Linux AArch64 integration targets; unchanged gate classifier and target environment policy, external anchored zero-grace RSS/timeout supervisor. Not whole-system acceptance.',started=datetime.now(timezone.utc).isoformat(),provenance=provenance,dependency_identity=deps,resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,timeout_seconds=1200,required_targets=gate.TARGETS,targets=[],complete=False,environment={k:os.environ[k] for k in ['PATH','RUSTUP_TOOLCHAIN','CARGO_TARGET_DIR','CARGO_BUILD_JOBS','RUST_TEST_THREADS','RUST_MIN_STACK']},harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),gate_sha256=hashlib.sha256((p/'scripts/check_linux_aarch64.py').read_bytes()).hexdigest(),tools_before=tool_observations(),installed_identity=installed)
def save():
 temporary=out/'results.json.tmp';temporary.write_text(json.dumps(record,indent=2)+'\n');temporary.replace(out/'results.json')
save()
for package,target in gate.TARGETS:
 command=['cargo','test','--locked','--offline','--color','never','-j','2','-p',package,'--test',target,'--','--nocapture','--test-threads=1']
 env=os.environ.copy()
 for key in gate.target_unset_environment(package,target):env.pop(key,None)
 print('RUN',package,target,flush=True)
 log_path=out/(package+'--'+target+'.log')
 result=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(log_path),*command],16384,1200,label=target,env=env,cwd=p)
 details=dataclasses.asdict(result) if dataclasses.is_dataclass(result) else result._asdict()
 (out/(target+'.capture.json')).write_text(json.dumps(details,indent=2)+'\n')
 log=log_path.read_bytes();verdict=gate.classify_result(result.returncode,log.decode(errors='replace'))
 if result.timed_out or result.memout or result.cancelled or result.stdout_truncated or result.stderr_truncated:
  verdict['status']='fail';verdict['errors'].append('incomplete or resource-limited execution')
 for key in ['stdout','stderr']:details.pop(key,None)
 row=dict(package=package,target=target,command=command,execution=details,log=log_path.name,log_sha256=hashlib.sha256(log).hexdigest(),unset_environment=list(gate.target_unset_environment(package,target)),**verdict)
 record['targets'].append(row);save();print(json.dumps(dict(target=target,status=row['status'],seconds=result.wall_sec,errors=row['errors'])),flush=True)
record['tools_after']=tool_observations();record['tools_unchanged']=record['tools_after']==record['tools_before']
record['final_source']=gate.source_provenance(provenance['tools']['git']);record['source_unchanged']=record['final_source']['source_fingerprint']==provenance['source_fingerprint']
record['final_dependency_identity']=gate.dependency_identity(provenance['tools']['git']);record['dependency_changes']=gate.dependency_recorder().identity_changes(deps,record['final_dependency_identity'])
record['complete']=len(record['targets'])==len(gate.TARGETS)
record['passed']=record['complete'] and record['source_unchanged'] and record['tools_unchanged'] and not record['dependency_changes'] and all(x['status']=='pass' for x in record['targets'])
record['finished']=datetime.now(timezone.utc).isoformat();save();raise SystemExit(0 if record['passed'] else 1)
