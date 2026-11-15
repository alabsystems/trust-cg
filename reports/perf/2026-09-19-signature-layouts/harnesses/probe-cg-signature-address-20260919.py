from pathlib import Path
import hashlib,importlib.util,json,os,signal,subprocess,sys,time
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-source-capture-20260917');out=r/'cg-signature-layouts-address-probe';out.mkdir()
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
backend=r/'cg-signature-layouts-capture-first/librustc_codegen_trust_cg.so'
source=r/'cg-signature-layouts-capture-first/ordered_address.rs'
cmd=[provenance['compiler_path'],'--edition=2024','--crate-type=lib','--emit=obj','-Cpanic=abort','--target','aarch64-unknown-linux-gnu','-Copt-level=1','-Ztrust-verify=off','-Zcodegen-backend='+str(backend),str(source),'-o',str(out/'probe.o')]
code,log=run('address',cmd)
for line in log.splitlines():
 if 'OUTPUT_SOURCE_MODULE=' in line:
  m=json.loads(line.split('OUTPUT_SOURCE_MODULE=',1)[1]);(out/'module.json').write_text(json.dumps(m,indent=2)+'\n');print(m['target_info']);print(m.get('tuple_layouts'))
  for block in m['functions'][0]['blocks']:
   for node in block['body']:print(node['inst'])
