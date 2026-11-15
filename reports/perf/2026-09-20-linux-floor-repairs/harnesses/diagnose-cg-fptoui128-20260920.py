from pathlib import Path
import dataclasses,hashlib,json,os,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917');out=r/'cg-fptoui128-baseline';out.mkdir();(out/'bin').mkdir()
wrapper='''#!/usr/bin/python3
from pathlib import Path
import json,shutil,subprocess,sys
out=Path('/home/ayates/trust-cg-soundness-20260914/cg-fptoui128-baseline')
args=sys.argv[1:]
(out/'cc-command.json').write_text(json.dumps(['/usr/bin/cc',*args],indent=2)+'\\n')
for value in args:
 path=Path(value)
 if path.is_file() and path.suffix in ['.o','.c']:shutil.copyfile(path,out/path.name)
result=subprocess.run(['/usr/bin/cc',*args])
if result.returncode==0 and '-o' in args:shutil.copy2(args[args.index('-o')+1],out/'runner')
sys.exit(result.returncode)
'''
(out/'bin/cc').write_text(wrapper);(out/'bin/cc').chmod(0o755)
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Capture unsigned i128 saturation wrong-result case')
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_')) and k not in ['RUSTC','RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_TARGET']}
env.update(PATH=str(out/'bin')+':/home/ayates/.rustup/toolchains/1.97.1-aarch64-unknown-linux-gnu/bin:/home/ayates/.local/bin:/home/ayates/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='1.97.1',CARGO_TARGET_DIR='$HOME/trust-cg/target',CARGO_BUILD_JOBS='2',RUST_TEST_THREADS='1',RUST_MIN_STACK='16777216')
rows=[]
for name,command,expected in [('test',['cargo','test','--locked','--offline','-p','trust-cg-codegen','--test','e2e_aarch64_fptosi_sat_i128','-j','2','--','--nocapture','--test-threads=1'],101),('captured-native',[str(out/'runner')],2)]:
 result=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(out/(name+'.log')),*command],16384,600,label=name,env=env,cwd=p)
 row=dataclasses.asdict(result);row.update(command=command,expected_exit=expected);rows.append(row)
 (out/'results.json').write_text(json.dumps(dict(scope='Expected failing baseline; wrapper forwards exact cc arguments and retains objects before test cleanup',resources=plan._asdict(),results=rows),indent=2)+'\n')
 assert not(result.memout or result.timed_out or result.cancelled or result.stdout_truncated or result.stderr_truncated) and result.returncode==expected
print((out/'captured-native.log').read_text(),flush=True)
