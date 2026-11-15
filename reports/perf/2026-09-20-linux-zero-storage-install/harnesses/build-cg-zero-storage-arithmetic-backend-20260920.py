from pathlib import Path
import hashlib,importlib.util,json,os,signal,subprocess,sys,time
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917');out=r/('cg-zero-storage-backend-'+sys.argv[1]);out.mkdir()
sealed=Path('/home/ayates/toolchains/trust-a62ae50d');assert Path('/home/ayates/.rustup/toolchains/trust').resolve()==sealed
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Linux zero-storage leaf repair: genuine Trust private backend build')
pack=Path(json.loads((r/'installed-aot-arithmetic-first/identity.json').read_text())['directory'])
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_')) and k not in ['RUSTC','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_RUSTC','CARGO_BUILD_RUSTC_WRAPPER','CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER','CARGO_BUILD_TARGET']}
env.update(PATH=str(r/'cg-output-memory-tools-first/bin')+':'+str(pack/'bin')+':'+str(sealed/'bin')+':/home/ayates/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='trust',CARGO_BUILD_JOBS='2',RUST_TEST_THREADS='1',RUST_MIN_STACK='16777216',XDG_CACHE_HOME=str(out/'cache'))
os.environ.clear();os.environ.update(env);os.chdir(p)
spec=importlib.util.spec_from_file_location('native_bridge_gate',p/'scripts/check_linux_aarch64_bridge.py');gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
target=r/'sealed-aarch64-bridge-target';provenance=gate.preflight(target)
record=dict(source=subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip(),tested_tree=subprocess.check_output(['git','write-tree'],cwd=p,text=True).strip(),provenance=provenance,resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,scope='Build the actual Trust private backend with zero-storage leaf frame repair. Explicit unverified Trust frontend build; backend proof checks unchanged. This build alone supplies no native execution or Rust writer admission credit.')
(out/'request.json').write_text(json.dumps(record,indent=2)+'\n')
cmd=[provenance['tools']['env'],'CARGO_TARGET_DIR='+str(target),'RUSTC='+provenance['compiler_path'],provenance['tools']['targo'],'--unverified','build','--manifest-path',str(gate.MANIFEST),'--target-dir',str(target),'--release','--locked','--color','never','-j','2','--message-format=json-render-diagnostics']
result=guard.run_captured(cmd,16384,7200,label='Arithmetic-preserving private backend build',env=env,cwd=p)
(out/'build.log').write_text(result.stdout+result.stderr)
record.update(command=cmd,exit_code=result.returncode,seconds=result.wall_sec,rss_breached=result.memout,guard_evidence=result.guard_evidence)
assert not(result.memout or result.timed_out or result.cancelled or result.stdout_truncated or result.stderr_truncated)
code=result.returncode
record['build']=gate.classify_build(code,(out/'build.log').read_text(),gate.MANIFEST,target/'release'/gate.BACKEND_NAME)
(out/'results.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:record[k] for k in ['exit_code','seconds','rss_breached','build']}),flush=True)
assert not result.memout and record['build']['status']=='pass',record['build']
gate.ensure_unchanged_source(record,'source_after_build')
backend=out/gate.BACKEND_NAME;record['backend']=gate.snapshot_backend(target/'release'/gate.BACKEND_NAME,backend,gate.backend_identity(target/'release'/gate.BACKEND_NAME))
record.update(complete=True,passed=True)
(out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
