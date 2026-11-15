from pathlib import Path
import dataclasses,hashlib,importlib.util,json,os,signal,subprocess,sys,time
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-source-capture-20260917');out=r/('cg-const-references-capture-'+sys.argv[1]);out.mkdir(exist_ok=True);assert not any(out.iterdir())
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip();sealed=Path('/home/ayates/toolchains/trust-a62ae50d')
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()==head
tested_tree=subprocess.check_output(['git','write-tree'],cwd=p,text=True).strip()
assert Path('/home/ayates/.rustup/toolchains/trust').resolve()==sealed
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Fresh canonical allocation images')
pack=Path(json.loads((r/'installed-zero-storage-second/identity.json').read_text())['directory'])
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_')) and k not in ['RUSTC','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_RUSTC','CARGO_BUILD_RUSTC_WRAPPER','CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER','CARGO_BUILD_TARGET']}
env.update(PATH=str(r/'cg-output-memory-tools-first/bin')+':'+str(pack/'bin')+':'+str(sealed/'bin')+':/home/ayates/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='trust',CARGO_BUILD_JOBS='2',RUST_TEST_THREADS='1',RUST_MIN_STACK='16777216',XDG_CACHE_HOME=str(out/'cache'))
os.environ.clear();os.environ.update(env);os.chdir(p)
spec=importlib.util.spec_from_file_location('native_bridge_gate',p/'scripts/check_linux_aarch64_bridge.py');gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
target=r/'sealed-aarch64-bridge-target';provenance=gate.preflight(target)
record=dict(source=head,tested_tree=tested_tree,provenance=provenance,resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,scope='Temporary diagnostic backend with canonical immutable-reference constants. Capture original TrustIR before unchanged proof enforcement; no native execution claim.',commands=[], cases=[])
(out/'request.json').write_text(json.dumps(record,indent=2)+'\n')
def save(): (out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
def run(name,cmd,timeout=300):
 wrapper=['python3',str(r/'run-command-to-log.py'),str(out/(name+'.log')),*cmd]
 result=guard.run_captured(wrapper,16384,timeout,label=name,env=env,cwd=p)
 row=dataclasses.asdict(result);row.update(name=name,command=cmd)
 record['commands'].append(row);save();print(json.dumps({k:v for k,v in row.items() if k not in ['stdout','stderr']}),flush=True)
 assert not any([result.timed_out,result.memout,result.cancelled,result.stdout_truncated,result.stderr_truncated])
 return result.returncode,(out/(name+'.log')).read_text()
cmd=[provenance['tools']['env'],'CARGO_TARGET_DIR='+str(target),'RUSTC='+provenance['compiler_path'],provenance['tools']['targo'],'--unverified','build','--manifest-path',str(gate.MANIFEST),'--target-dir',str(target),'--release','--locked','--color','never','-j','2','--message-format=json-render-diagnostics']
code,log=run('build-backend',cmd,7200);record['build']=gate.classify_build(code,log,gate.MANIFEST,target/'release'/gate.BACKEND_NAME);assert record['build']['status']=='pass',record['build']
gate.ensure_unchanged_source(record,'source_after_build');backend=out/gate.BACKEND_NAME;record['backend']=gate.snapshot_backend(target/'release'/gate.BACKEND_NAME,backend,gate.backend_identity(target/'release'/gate.BACKEND_NAME));save()

sources=r/'cg-const-references-sources'
record['instrumentation_patch_sha256']=hashlib.sha256((r/'cg-const-references-instrumentation-final.patch').read_bytes()).hexdigest()
for original in sorted(sources.glob('*.rs')):
 source=out/original.name;source.write_bytes(original.read_bytes())
 for opt in [0,1]:
  name=original.stem+'-O'+str(opt);folder=out/name;folder.mkdir()
  cmd=[provenance['compiler_path'],'--edition=2024','--crate-type=lib','--emit=obj',('-Cpanic=unwind' if original.stem=='bounds_unwind' else '-Cpanic=abort'),'--target','aarch64-unknown-linux-gnu',f'-Copt-level={opt}','-Ztrust-verify=off','-Zcodegen-backend='+str(backend),str(source),'-o',str(folder/(name+'.o'))]
  code,log=run(name,cmd)
  modules=[json.loads(line.split('OUTPUT_SOURCE_MODULE=',1)[1]) for line in log.splitlines() if 'OUTPUT_SOURCE_MODULE=' in line]
  for index,module in enumerate(modules):(out/(name+f'-module{index}.trust-ir.json')).write_text(json.dumps(module,indent=2)+'\n')
  objects=[dict(path=str(f.relative_to(out)),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size) for f in sorted(folder.glob('*.o'))]
  record['cases'].append(dict(name=name,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),exit_code=code,source_captured=bool(modules),module_count=len(modules),production_admitted=code==0,proof_refusal='TCG-PROOF-465' in log,objects=objects))
  save()
gate.ensure_unchanged_source(record,'source_after_capture')
record.update(complete=True,observed=True)
save();print(json.dumps(record['cases']),flush=True)
