from pathlib import Path
import dataclasses,hashlib,json,os,subprocess,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');out=r/('ay-shadow-'+sys.argv[1]);out.mkdir()
cwd=Path(sys.argv[2]);command=sys.argv[3:]
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Checked shadowed array stores')
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_')) and k not in ['RUSTC','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS']}
env.update(RUSTUP_TOOLCHAIN='1.97.1',RUSTFLAGS='-C target-cpu=native',CARGO_BUILD_JOBS='2',RUST_TEST_THREADS='1',RUST_MIN_STACK='16777216',CARGO_TARGET_DIR='/home/ayates/ay-pblendvb-export-20260914/export/target')
def identity():
    if (cwd/'.git').exists():
        return {'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=cwd,text=True).strip(),'diff_sha256':hashlib.sha256(subprocess.check_output(['git','diff','HEAD'],cwd=cwd)).hexdigest()}
    return {str(p.relative_to(cwd)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(cwd.rglob('*')) if p.is_file() and 'target' not in p.parts}
before=identity();record=dict(command=command,cwd=str(cwd),before=before,resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,complete=False)
(out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
result=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(out/'command.log'),*command],16384,1800,label=out.name,env=env,cwd=cwd)
record.update(result=dataclasses.asdict(result),inputs_unchanged=before==identity(),complete=not any([result.memout,result.timed_out,result.cancelled,result.stdout_truncated,result.stderr_truncated]))
record['passed']=record['complete'] and record['inputs_unchanged'] and result.returncode==0
(out/'result.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:v for k,v in record.items() if k!='before'}),flush=True)
sys.exit(0 if record['passed'] else 1)
