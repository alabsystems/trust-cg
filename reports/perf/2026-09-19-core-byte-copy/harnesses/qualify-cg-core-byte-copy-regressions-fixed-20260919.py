from pathlib import Path
import hashlib,json,os,re,signal,subprocess,sys,time
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917');out=r/('cg-core-byte-copy-'+sys.argv[1]);out.mkdir();ir_rev=sys.argv[2]
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
resources=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='CG typed pointer Copy repair and canonical byte replay adoption')
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_')) and k not in ['RUSTC','RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_TARGET']}
env.update(RUSTUP_TOOLCHAIN='1.97.1',CARGO_BUILD_JOBS='2',RUST_TEST_THREADS='1',RUST_MIN_STACK='16777216',CARGO_TARGET_DIR='$HOME/trust-cg/target')
stock=Path(subprocess.check_output(['rustup','run','1.97.1','rustc','--print','sysroot'],text=True).strip())/'bin';env['PATH']=str(stock)+':/home/ayates/.cargo/bin:/usr/bin:/bin'
def git(*args):return subprocess.check_output(['git',*args],cwd=p,text=True).strip()
def inventory():
 names=set(git('ls-files').splitlines())|set(git('ls-files','--others','--exclude-standard').splitlines())
 return {n:hashlib.sha256((p/n).read_bytes()).hexdigest() for n in names if n.endswith(('.rs','.toml','Cargo.lock','.sh','.py'))}
head=git('rev-parse','HEAD')
def run(label,command,expected=None):
 before=inventory();record=dict(head=head,command=command,resources=resources._asdict(),environment={k:env[k] for k in ['PATH','RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','RUST_TEST_THREADS','RUST_MIN_STACK','CARGO_TARGET_DIR']},rss_limit_mb=16384,grace_mb=0)
 (out/(label+'.request.json')).write_text(json.dumps(dict(**record,inputs=before),indent=2)+'\n');start=time.monotonic()
 with (out/(label+'.log')).open('w') as log:
  proc=subprocess.Popen(command,cwd=p,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);watch=guard.rss_watchdog(proc,16384,label=label,grace_mb=0)
  try:code=proc.wait(timeout=7200)
  except BaseException:os.killpg(proc.pid,signal.SIGKILL);proc.wait();raise
  finally:watch.stop()
 record.update(exit_code=code,seconds=time.monotonic()-start,rss_breached=watch.breached,inputs_unchanged=inventory()==before,head_unchanged=git('rev-parse','HEAD')==head,tests=re.findall(r'^test result:.*$',(out/(label+'.log')).read_text(),re.M))
 (out/(label+'.results.json')).write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record),flush=True)
 assert code==0 and not watch.breached and record['head_unchanged']
 if label!='pin':assert record['inputs_unchanged']
 if expected is not None:
  assert len(record['tests'])==1
  match=re.search(r'test result: ok\. (\d+) passed; 0 failed; 0 ignored;',record['tests'][0]);assert match and (int(match[1])==expected if expected>0 else int(match[1])>=abs(expected))
 return record
results=[]
(out/'qualified-source.patch').write_bytes(subprocess.check_output(['git','diff','--binary','HEAD'],cwd=p))
results.append(run('bridge-copy',['cargo','test','--locked','-p','trust-cg-verify','--test','bridge_copy_types','-j','2','--','--nocapture','--test-threads=1'],3))
results.append(run('source-output-regressions',['cargo','test','--locked','-p','trust-cg-verify','--lib','-j','2','source_bound_frame::output_memory::','--','--nocapture','--test-threads=1'],-10))
results.append(run('canonical-store',['python3','scripts/check_core_byte_store.py','--output',str(out/'canonical-store-gate')]))
report=json.loads((out/'canonical-store-gate/report.json').read_text());assert report['passed']
(out/'results.json').write_text(json.dumps(dict(passed=True,head=head,trust_ir=ir_rev,scope='Canonical kernel Store/Return replay plus exact source-copy normalization and typed diagnostic binding; no native frontend or publication claim.',results=results),indent=2)+'\n')
