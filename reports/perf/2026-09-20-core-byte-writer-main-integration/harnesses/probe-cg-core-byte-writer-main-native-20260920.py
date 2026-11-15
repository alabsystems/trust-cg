from pathlib import Path
import hashlib,json,os,signal,subprocess,sys,time
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917');out=r/'cg-core-byte-writer-main-native-first';out.mkdir()
build=json.loads((r/'cg-core-byte-writer-main-backend-first/results.json').read_text());assert build['passed']
sealed=Path('/home/ayates/toolchains/trust-a62ae50d');backend=r/'cg-core-byte-writer-main-backend-first/librustc_codegen_trust_cg.so'
pack=Path(json.loads((r/'installed-aot-arithmetic-first/identity.json').read_text())['directory'])
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_')) and k not in ['RUSTC','RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_TARGET']}
env.update(PATH=str(r/'cg-output-memory-tools-first/bin')+':'+str(pack/'bin')+':'+str(sealed/'bin')+':/home/ayates/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='trust',RUST_TEST_THREADS='1',RUST_MIN_STACK='16777216',XDG_CACHE_HOME=str(out/'cache'))
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Merged-main ordinary writer refusal and scalar admission control')
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip();assert head==build['source']
record=dict(source=head,scope='Ordinary uninstrumented Trust backend, explicit unverified Rust frontend, backend proof checks enabled. Writer refusal is not successful compiler admission.',backend_sha256=hashlib.sha256(backend.read_bytes()).hexdigest(),resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,cases=[])
(out/'request.json').write_text(json.dumps(record,indent=2)+'\n')
for name,source in [('writer','output_memory_writer.rs'),('scalar','scalar_batch.rs')]:
 folder=out/name;folder.mkdir();src=folder/source;src.write_bytes((r/'cg-signature-layouts-capture-fourth'/source).read_bytes())
 command=[str(sealed/'bin/trustc'),'--edition=2024','--crate-type=lib','--emit=obj','-Cpanic=abort','--target','aarch64-unknown-linux-gnu','-Copt-level=1','-Ztrust-verify=off','-Zcodegen-backend='+str(backend),str(src),'-o',str(folder/(name+'.o'))]
 start=time.monotonic()
 with (folder/'compile.log').open('w') as log:
  proc=subprocess.Popen(command,cwd=folder,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);watch=guard.rss_watchdog(proc,16384,label=name,grace_mb=0)
  try:code=proc.wait(timeout=180)
  except BaseException:os.killpg(proc.pid,signal.SIGKILL);proc.wait();raise
  finally:watch.stop()
 text=(folder/'compile.log').read_text();objects=[dict(path=str(f.relative_to(out)),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size) for f in sorted(folder.glob('*.o'))]
 case=dict(name=name,command=command,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),exit_code=code,seconds=time.monotonic()-start,rss_breached=watch.breached,proof_refusal='TCG-PROOF-465' in text,production_admitted=code==0,objects=objects)
 record['cases'].append(case);(out/'results.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(case),flush=True)
 assert not watch.breached
 if name=='writer':assert code==1 and case['proof_refusal'] and not objects
 else:assert code==0 and objects
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()==head
record['expected_results_observed']=True
(out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
