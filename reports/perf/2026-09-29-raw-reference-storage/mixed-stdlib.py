from pathlib import Path
import os,subprocess,json,sys,time,signal
p=Path('$HOME/trust-cg/target/reference-raw-reborrow-investigation')
inputs=p.parent/'std-build-investigation'
exec((p/'env.py').read_text())
lane=sys.argv[1];label=sys.argv[2] if len(sys.argv)>2 else lane
d=p/label;d.mkdir(exist_ok=True)
flags=['-Ztrust-verify=off','-Zforce-unstable-if-unmarked','-Ccodegen-units=1']
backend=Path(sys.argv[3]).resolve() if len(sys.argv)>3 else p.parent/'optimized-alloc-investigation/second-backend.so'
if lane=='cg':flags+=['-Zcodegen-backend='+str(backend),'-Ztrust-ir-cg-args=diag-json no-proof-certs']
env.update(STD_CORE_OPT=(sys.argv[4] if len(sys.argv)>4 else '0'),STD_CORE_BACKEND=str(backend),CARGO_TARGET_DIR=str(d/'target'),CARGO_ENCODED_RUSTFLAGS='\x1f'.join(flags),RUSTC_WRAPPER=str(p/'mixed-compiler-wrapper.py'),STD_BUILD_RECORDS=str(d/'invocations'),CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_DEV_OPT_LEVEL='0',CARGO_PROFILE_DEV_CODEGEN_UNITS='1')
cmd=[str(tc/'bin/targo'),'--unverified','build','--manifest-path',str(inputs/'source/library/Cargo.toml'),'-p','std','--lib','--features=backtrace,panic-unwind','--target=aarch64-unknown-linux-gnu','--locked','--offline','-j','2','--message-format=json','--keep-going','-vv']
if label=='llvm-resolve':cmd.remove('--locked')
start=time.monotonic();timedout=False
with (d/'build.log').open('wb') as log:
 process=subprocess.Popen(cmd,cwd=inputs/'source/library',env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 try:code=process.wait(timeout=600)
 except subprocess.TimeoutExpired:
  timedout=True;os.killpg(process.pid,signal.SIGTERM)
  try:code=process.wait(timeout=10)
  except subprocess.TimeoutExpired:os.killpg(process.pid,signal.SIGKILL);code=process.wait()
(p/(label+'-results.json')).write_text(json.dumps(dict(lane=lane,command=cmd,environment={k:env[k] for k in ['CARGO_ENCODED_RUSTFLAGS','RUSTC','RUSTC_WRAPPER','RUSTC_BOOTSTRAP','CARGO_TARGET_DIR','CARGO_PROFILE_DEV_DEBUG','CARGO_PROFILE_DEV_OPT_LEVEL','CARGO_PROFILE_DEV_CODEGEN_UNITS','STD_BUILD_RECORDS','STD_CORE_BACKEND','STD_CORE_OPT']},returncode=code,wall_seconds=time.monotonic()-start,timed_out=timedout),indent=2)+'\n')
print(label,code,timedout,flush=True)
raise SystemExit(code)
