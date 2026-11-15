from pathlib import Path
import hashlib,importlib.util,json,os,signal,subprocess,sys,time
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-source-capture-20260917');out=r/('cg-signature-layouts-capture-'+sys.argv[1]);out.mkdir(exist_ok=True);assert not any(out.iterdir())
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip();sealed=Path('/home/ayates/toolchains/trust-a62ae50d')
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()==head
tested_tree=subprocess.check_output(['git','write-tree'],cwd=p,text=True).strip()
assert Path('/home/ayates/.rustup/toolchains/trust').resolve()==sealed
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Fresh rustc signature layout capture')
pack=Path(json.loads((r/'installed-aot-arithmetic-first/identity.json').read_text())['directory'])
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_')) and k not in ['RUSTC','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_RUSTC','CARGO_BUILD_RUSTC_WRAPPER','CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER','CARGO_BUILD_TARGET']}
env.update(PATH=str(r/'cg-output-memory-tools-first/bin')+':'+str(pack/'bin')+':'+str(sealed/'bin')+':/home/ayates/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='trust',CARGO_BUILD_JOBS='2',RUST_TEST_THREADS='1',RUST_MIN_STACK='16777216',XDG_CACHE_HOME=str(out/'cache'))
os.environ.clear();os.environ.update(env);os.chdir(p)
spec=importlib.util.spec_from_file_location('native_bridge_gate',p/'scripts/check_linux_aarch64_bridge.py');gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
target=r/'sealed-aarch64-bridge-target';provenance=gate.preflight(target)
record=dict(source=head,tested_tree=tested_tree,provenance=provenance,resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,scope='Temporary diagnostic backend with production rustc signature layout metadata. Capture original TrustIR before unchanged proof enforcement; no native execution claim.',commands=[], cases=[])
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

sources=r/'cg-signature-layout-sources'
record['instrumentation_patch_sha256']=hashlib.sha256((r/'cg-signature-layouts-instrumentation.patch').read_bytes()).hexdigest()
def capture(name,source,opt):
 obj=out/(name+'.o')
 cmd=[provenance['compiler_path'],'--edition=2024','--crate-type=lib','--emit=obj','-Cpanic=abort','--target','aarch64-unknown-linux-gnu',f'-Copt-level={opt}','-Ztrust-verify=off','-Zcodegen-backend='+str(backend),str(source),'-o',str(obj)]
 code,log=run(name,cmd)
 modules=[json.loads(line.split('OUTPUT_SOURCE_MODULE=',1)[1]) for line in log.splitlines() if 'OUTPUT_SOURCE_MODULE=' in line]
 assert len(modules)==1,(name,len(modules))
 module=modules[0]
 (out/(name+'.trust-ir.json')).write_text(json.dumps(module,indent=2)+'\n')
 record['cases'].append(dict(name=name,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),exit_code=code,source_captured=True,production_admitted=code==0,proof_refusal='[TCG-PROOF-465]' in log,object_exists=obj.is_file()))
 save()
 return module
source=out/'output_memory_writer.rs';source.write_bytes((p/'crates/trust-cg-verify/tests/fixtures/output_memory_writer.rs').read_bytes())
for opt in range(4):
 name=f'writer-O{opt}'
 module=capture(name,source,opt)
 old=json.loads((r/'cg-copy-source-capture-first'/(name+'.trust-ir.json')).read_text())
 assert module['target_info']==dict(triple='aarch64-unknown-linux-gnu',pointer_size=8,endianness='Little',abi=None,struct_passing='NativeC')
 assert module['types']==old['types']+[dict(Tuple=['U64']*5)]
 assert module['tuple_layouts']==[dict(tuple_type=5,size=40,align=8,field_offsets=[0,8,16,24,32])]
 comparable=dict(module)
 for field in ['types','tuple_layouts','target_info']:comparable[field]=old.get(field)
 # Older captures serialized before tuple layouts were emitted may omit empty metadata.
 if 'tuple_layouts' not in old: comparable.pop('tuple_layouts')
 assert comparable==old, name
 record['cases'][-1]['only_target_and_tuple_metadata_changed']=True
 save()
expectations=json.loads((sources/'expectations.json').read_text())
for name,offsets in expectations.items():
 source=out/(name+'.rs');source.write_bytes((sources/(name+'.rs')).read_bytes())
 module=capture(name,source,1)
 assert module['target_info']['pointer_size']==8
 if offsets:
  assert len(module['tuple_layouts'])==1,(name,module['tuple_layouts'])
  descriptor=module['tuple_layouts'][0]
  assert descriptor['size']==16 and descriptor['align']==8 and descriptor['field_offsets']==offsets,(name,descriptor)
  assert module['types'][descriptor['tuple_type']]==dict(Tuple=['U8','U64'])
  assert module['target_info']['struct_passing']=='NativeC'
 else:
  assert not module.get('tuple_layouts'),(name,module.get('tuple_layouts'))
  assert module['target_info']['struct_passing']==('NativeC' if offsets==[] else 'Unclassified'),name
 record['cases'][-1]['expected_layout_metadata']=True
 save()
source=out/'layout_oracle.rs';source.write_bytes((sources/'layout_oracle.rs').read_bytes())
code,_=run('layout-oracle-build',[provenance['compiler_path'],'--edition=2024','-Copt-level=1','-Ztrust-verify=off',str(source),'-o',str(out/'layout-oracle')])
assert code==0
code,log=run('layout-oracle',[str(out/'layout-oracle')]);assert code==0
assert log.splitlines()==['ordered 16 8 0 8','reordered 16 8 8 0','packed 9 1 0 1','nested 24 8 0 16'],log
record['independent_llvm_layout_oracle']=True
gate.ensure_unchanged_source(record,'source_after_capture')
record.update(complete=True,passed=len(record['cases'])==14,scope='Actual Trust frontend captures four writer optimization levels and ten layout/ABI controls. Independent LLVM-backed offset_of/size_of/align_of program checks source layout values. Source metadata checks do not confer native compilation or memory-access authority; compile outcomes retained separately.')
save();print(json.dumps(record['cases']),flush=True)
