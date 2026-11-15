from pathlib import Path
import dataclasses,json,os,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917');out=r/'cg-floor-jit-baseline';out.mkdir()
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
resources=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Isolate JIT baseline failures without LLVM environment override')
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_')) and k not in ['RUSTC','RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_TARGET']}
env.update(PATH='/home/ayates/.rustup/toolchains/1.97.1-aarch64-unknown-linux-gnu/bin:/home/ayates/.local/lib/trust-cg/47c6c194-ay43f133d3-cleaned2a80d1/bin:/home/ayates/.cargo/bin:/home/ayates/.local/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='1.97.1',CARGO_TARGET_DIR='$HOME/trust-cg/target',CARGO_BUILD_JOBS='2',RUST_TEST_THREADS='1',RUST_MIN_STACK='16777216')
rows=[]
for target,expected in [('core_jit_planning',0),('jit_fail_closed_proof_policy',101)]:
 command=['cargo','test','--locked','--offline','-p','trust-cg-codegen','--test',target,'-j','2','--','--nocapture','--test-threads=1'];log=out/(target+'.log')
 result=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(log),*command],16384,600,label=target,env=env,cwd=p)
 row=dataclasses.asdict(result);row.update(command=command,expected_exit=expected);rows.append(row)
 (out/'results.json').write_text(json.dumps(dict(scope='Baseline diagnosis, JIT proof regression is an expected FAILURE, not passing qualification',resources=resources._asdict(),rss_limit_mb=16384,grace_mb=0,results=rows),indent=2)+'\n')
 assert not(result.memout or result.timed_out or result.cancelled or result.stdout_truncated or result.stderr_truncated) and result.returncode==expected
 if expected==101:assert 'no non-vacuous proof-grade' in log.read_text()
print('Clean environment: Core admission passes; proof-required identity failure reproduces',flush=True)
