from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917');out=r/'cg-live-frame-release-first';out.mkdir()
def git(*args):return subprocess.check_output(['git',*args],cwd=p,text=True).strip()
head=git('rev-parse','HEAD');assert not git('status','--porcelain')
for folder in ['cg-live-frame-tests-fifth','cg-live-frame-tests-seventh','cg-live-frame-tests-ninth']:assert json.loads((r/folder/'results.json').read_text())['passed']
assert json.loads((r/'cg-live-frame-bounds-native-first/results.json').read_text())['passed']
source=json.loads((r/'cg-live-frame-source.json').read_text())
for name,sha in source['files'].items():assert hashlib.sha256((p/name).read_bytes()).hexdigest()==sha
names=git('ls-files').splitlines()
def inventory():return {n:hashlib.sha256((p/n).read_bytes()).hexdigest() for n in names if n.endswith(('.rs','.toml','Cargo.lock'))}
before=inventory()
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_')) and k not in ['RUSTFLAGS','RUSTC','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_TARGET','CARGO_BUILD_RUSTC','CARGO_BUILD_RUSTC_WRAPPER','CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER']}
env.update(RUSTUP_TOOLCHAIN='1.97.1',CARGO_BUILD_JOBS='2',RUST_TEST_THREADS='1',RUST_MIN_STACK='16777216',PATH='/home/ayates/.rustup/toolchains/1.97.1-aarch64-unknown-linux-gnu/bin:/home/ayates/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR='$HOME/trust-cg/target')
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Qualified global-address compiler CLI build')
command=['cargo','build','--release','--locked','--bin','trust-cg','-j','2']
record=dict(source=head,scope='Stock Rust development CLI; qualified frame/pipeline and genuine Trust backend source. Installation requires separate current CLI preflight. Not verified self-hosting.',command=command,inputs=before,resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0)
(out/'request.json').write_text(json.dumps(record,indent=2)+'\n')
result=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(out/'build.log'),*command],16384,5400,label='Compiler CLI release',env=env,cwd=p)
record.pop('inputs');record.update(exit_code=result.returncode,seconds=result.wall_sec,guard_evidence=result.guard_evidence,inputs_unchanged=inventory()==before,head_after=git('rev-parse','HEAD'),status_after=git('status','--porcelain'),timed_out=result.timed_out,memout=result.memout,cancelled=result.cancelled)
(out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
assert not (result.returncode or result.timed_out or result.memout or result.cancelled or result.stdout_truncated or result.stderr_truncated)
assert record['inputs_unchanged'] and record['head_after']==head and not record['status_after']
folder=r/('trust-cg-at-'+head[:8]);folder.mkdir();binary=folder/'trust-cg';shutil.copyfile('$HOME/trust-cg/target/release/trust-cg',binary);binary.chmod(0o555)
record.update(binary=str(binary),sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),passed=True)
for path in [folder/'identity.json',out/'result.json']:path.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['source','binary','sha256','seconds','passed']}),flush=True)
