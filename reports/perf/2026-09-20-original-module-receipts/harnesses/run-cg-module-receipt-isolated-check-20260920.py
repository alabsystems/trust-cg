from pathlib import Path
import dataclasses, hashlib, importlib.util, json, os, subprocess, sys
from datetime import datetime, timezone
r=Path('/home/ayates/trust-cg-soundness-20260914')
p=Path('/home/ayates/trust-cg-module-receipt-20260920')
out=r/('cg-module-receipt-'+sys.argv[1]); out.mkdir()
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts')
import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Original Module verification receipt identity')
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_')) and k not in ['RUSTFLAGS','RUSTC','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_TARGET','CARGO_BUILD_RUSTC','CARGO_BUILD_RUSTC_WRAPPER','CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER']}
env.update(PATH='/home/ayates/.rustup/toolchains/1.97.1-aarch64-unknown-linux-gnu/bin:/home/ayates/.cargo/bin:/home/ayates/.local/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='1.97.1',CARGO_BUILD_JOBS='2',RUST_TEST_THREADS='1',RUST_MIN_STACK='16777216',CARGO_TARGET_DIR='/home/ayates/trust-cg-module-receipt-20260920/target')
os.environ.clear();os.environ.update(env)
os.chdir(p)
spec=importlib.util.spec_from_file_location('linux_floor',p/'scripts/check_linux_aarch64.py')
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
source=gate.preflight()
cmd=sys.argv[2:]
log=out/'command.log'
record=dict(source=source,command=cmd,started=datetime.now(timezone.utc).isoformat(),resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,complete=False)
(out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
result=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(log),*cmd],16384,1200,label=out.name,env=env,cwd=p)
record['execution']=dataclasses.asdict(result)
record['final_source']=gate.source_provenance(source['tools']['git'])
record['source_unchanged']=record['final_source']['source_fingerprint']==source['source_fingerprint']
record.update(complete=True,passed=result.returncode==0 and not any([result.timed_out,result.memout,result.cancelled,result.stdout_truncated,result.stderr_truncated]) and record['source_unchanged'],finished=datetime.now(timezone.utc).isoformat())
(out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(passed=record['passed'],seconds=result.wall_sec,log=str(log))),flush=True)
sys.exit(0 if record['passed'] else 1)
