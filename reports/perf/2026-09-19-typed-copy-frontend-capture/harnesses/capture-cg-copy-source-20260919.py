from pathlib import Path
import hashlib,importlib.util,json,os,signal,subprocess,sys,time
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-source-capture-20260917');out=r/'cg-copy-source-capture-first';out.mkdir(exist_ok=True);assert not any(out.iterdir())
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip();sealed=Path('/home/ayates/toolchains/trust-a62ae50d')
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()==head
tested_tree=subprocess.check_output(['git','write-tree'],cwd=p,text=True).strip()
assert Path('/home/ayates/.rustup/toolchains/trust').resolve()==sealed
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Fresh typed Copy source capture from actual private backend')
pack=Path(json.loads((r/'installed-aot-arithmetic-first/identity.json').read_text())['directory'])
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_')) and k not in ['RUSTC','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_RUSTC','CARGO_BUILD_RUSTC_WRAPPER','CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER','CARGO_BUILD_TARGET']}
env.update(PATH=str(r/'cg-output-memory-tools-first/bin')+':'+str(pack/'bin')+':'+str(sealed/'bin')+':/home/ayates/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='trust',CARGO_BUILD_JOBS='2',RUST_TEST_THREADS='1',RUST_MIN_STACK='16777216',XDG_CACHE_HOME=str(out/'cache'))
os.environ.clear();os.environ.update(env);os.chdir(p)
spec=importlib.util.spec_from_file_location('native_bridge_gate',p/'scripts/check_linux_aarch64_bridge.py');gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
target=r/'sealed-aarch64-bridge-target';provenance=gate.preflight(target)
record=dict(source=head,tested_tree=tested_tree,provenance=provenance,resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,scope='Temporary diagnostic backend with the production typed Copy repair. Capture original TrustIR before unchanged proof enforcement; no native execution claim.',commands=[], cases=[])
(out/'request.json').write_text(json.dumps(record,indent=2)+'\n')
def save(): (out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
def run(name,cmd,timeout=300):
 start=time.monotonic();timed_out=False
 with (out/(name+'.log')).open('w') as log:
  proc=subprocess.Popen(cmd,cwd=p,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);watch=guard.rss_watchdog(proc,16384,label=name,grace_mb=0)
  try:code=proc.wait(timeout=timeout)
  except subprocess.TimeoutExpired:timed_out=True;os.killpg(proc.pid,signal.SIGKILL);code=proc.wait()
  finally:watch.stop()
 row=dict(name=name,command=cmd,exit_code=code,seconds=time.monotonic()-start,timed_out=timed_out,rss_breached=watch.breached);record['commands'].append(row);save();print(json.dumps(row),flush=True)
 assert not timed_out and not watch.breached
 return code,(out/(name+'.log')).read_text()
cmd=[provenance['tools']['env'],'CARGO_TARGET_DIR='+str(target),'RUSTC='+provenance['compiler_path'],provenance['tools']['targo'],'--unverified','build','--manifest-path',str(gate.MANIFEST),'--target-dir',str(target),'--release','--locked','--color','never','-j','2','--message-format=json-render-diagnostics']
code,log=run('build-backend',cmd,7200);record['build']=gate.classify_build(code,log,gate.MANIFEST,target/'release'/gate.BACKEND_NAME);assert record['build']['status']=='pass',record['build']
gate.ensure_unchanged_source(record,'source_after_build');backend=out/gate.BACKEND_NAME;record['backend']=gate.snapshot_backend(target/'release'/gate.BACKEND_NAME,backend,gate.backend_identity(target/'release'/gate.BACKEND_NAME));save()
source=out/'output_memory_writer.rs';source.write_bytes((p/'crates/trust-cg-verify/tests/fixtures/output_memory_writer.rs').read_bytes())
record['source_fixture_sha256']=hashlib.sha256(source.read_bytes()).hexdigest()
record['instrumentation_patch_sha256']=hashlib.sha256((r/'cg-copy-source-capture-instrumentation.patch').read_bytes()).hexdigest()
for opt in range(4):
 name=f'writer-O{opt}';obj=out/(name+'.o')
 command=[provenance['compiler_path'],'--edition=2024','--crate-type=lib','--emit=obj','-Cpanic=abort','--target','aarch64-unknown-linux-gnu',f'-Copt-level={opt}','-Ztrust-verify=off','-Zcodegen-backend='+str(backend),str(source),'-o',str(obj)]
 code,log=run(name,command)
 modules=[json.loads(line.split('OUTPUT_SOURCE_MODULE=',1)[1]) for line in log.splitlines() if 'OUTPUT_SOURCE_MODULE=' in line]
 assert len(modules)==1,(name,len(modules))
 (out/(name+'.trust-ir.json')).write_text(json.dumps(modules[0],indent=2)+'\n')
 nodes=[n for f in modules[0]['functions'] for b in f['blocks'] for n in b['body']]
 casts=[n for n in nodes if n['inst'].get('Cast',{}).get('op')=='PtrToPtr']
 assert len(casts)==5,(name,len(casts))
 expected={'RefMut':{'Tuple':['U64']*5}}
 for n in casts:
  assert n['inst']['Cast']==dict(op='PtrToPtr',src_ty=expected,dst_ty='Ptr',operand=1),n
 assert not any(n['inst'].get('Copy',{}).get('ty')=='Ptr' and n['inst'].get('Copy',{}).get('operand')==1 for n in nodes)
 record['cases'].append(dict(name=name,exit_code=code,source_captured=True,typed_reference_casts=len(casts),production_admitted=code==0,proof_refusal='[TCG-PROOF-465]' in log,object_exists=obj.is_file()))
 save()
gate.ensure_unchanged_source(record,'source_after_capture')
record.update(complete=True,passed=len(record['cases'])==4,scope='Temporary diagnostic backend captures four actual TrustIR modules from the unchanged ordinary Rust fixture at O0–O3 and verifies five explicit RefMut-to-Ptr casts in each. The ordinary proof path remains enabled; compile outcomes are recorded individually. Capturing source is not native execution or a frontend refinement proof.')
save();print(json.dumps(record['cases']),flush=True)
