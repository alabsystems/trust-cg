from pathlib import Path
import subprocess,json,sys,time,os,signal,hashlib
p=Path('$HOME/trust-cg/target/virtual-unwind-investigation')
inputs=p.parent/'std-build-investigation'
name=sys.argv[1];label=sys.argv[2];opt=int(sys.argv[3]) if len(sys.argv)>3 else 0
rows=[]
for f in (inputs/'llvm-resolve/invocations').glob('*.json'):
 r=json.loads(f.read_text());c=r['command']
 if '--crate-name' in c and c[c.index('--crate-name')+1]==name and '--target' in c:rows.append(r)
assert len(rows)==1,(name,len(rows));row=rows[0]
d=p/label;d.mkdir(exist_ok=True);backend=Path(sys.argv[4]).resolve() if len(sys.argv)>4 else p.parent/'optimized-alloc-investigation/second-backend.so'
cmd=row['command'].copy();cmd[cmd.index('--out-dir')+1]=str(d)
cmd+=['-Copt-level='+str(opt),'-Zcodegen-backend='+str(backend),'-Ztrust-ir-cg-args=diag-json no-proof-certs']
if len(sys.argv)>6 and sys.argv[6]=='profile':cmd[-1]+=' time-codegen=20 time-lower'
if len(sys.argv)>6 and sys.argv[6]=='dump':cmd[-1]+=' diag-dump'
env={**os.environ,**row['environment']}
for key in ['CARGO_MAKEFLAGS','MAKEFLAGS','MFLAGS']:env.pop(key,None)
start=time.monotonic();timedout=False
with (d/'compile.log').open('wb') as log:
 process=subprocess.Popen(cmd,cwd=row['cwd'],env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 try:code=process.wait(timeout=int(sys.argv[5]) if len(sys.argv)>5 else 300)
 except subprocess.TimeoutExpired:
  timedout=True;os.killpg(process.pid,signal.SIGTERM)
  try:code=process.wait(timeout=10)
  except subprocess.TimeoutExpired:os.killpg(process.pid,signal.SIGKILL);code=process.wait()
roots=[];diagnostics=[]
for line in (d/'compile.log').read_text().splitlines():
 if not line.startswith('{'):continue
 try:e=json.loads(line)
 except ValueError:continue
 if isinstance(e.get('code'),str):diagnostics.append(e)
 if e.get('code')=='TCG-MIR-UNSUPPORTED':roots=e['fields']['failed_roots'].split('\n  - ')
result=dict(command=cmd,cwd=row['cwd'],environment=row['environment'],returncode=code,wall_seconds=time.monotonic()-start,timeout_seconds=int(sys.argv[5]) if len(sys.argv)>5 else 300,timed_out=timedout,failed_roots=roots,diagnostics=diagnostics,backend_sha256=hashlib.sha256(backend.read_bytes()).hexdigest())
(p/(label+'-results.json')).write_text(json.dumps(result,indent=2)+'\n')
print(name,opt,code,'roots',len(roots),flush=True)

raise SystemExit(code)
