#!/usr/bin/python3
from pathlib import Path
import subprocess,sys,os,json,time
p=Path(os.environ['STD_BUILD_RECORDS']);p.mkdir(exist_ok=True)
args=sys.argv[1:];name='probe'
if '--crate-name' in args:name=args[args.index('--crate-name')+1]
if name=='core' and '--target' in args:args += ['-Zcodegen-backend='+os.environ['STD_CORE_BACKEND'],'-Ztrust-ir-cg-args=diag-json no-proof-certs','-Copt-level='+os.environ.get('STD_CORE_OPT','0')]
record=p/f'{name}-{os.getpid()}-{time.time_ns()}'
selected={k:v for k,v in os.environ.items() if k.startswith(('CARGO_','RUST','STD_','CFG_','LLVM_')) or k in ['OUT_DIR','LD_LIBRARY_PATH','PATH','TARGET','HOST','OPT_LEVEL','DEBUG','PROFILE']}
start=time.monotonic()
r=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
record.with_suffix('.stdout.log').write_bytes(r.stdout);record.with_suffix('.stderr.log').write_bytes(r.stderr)
record.with_suffix('.json').write_text(json.dumps(dict(command=args,cwd=os.getcwd(),environment=selected,returncode=r.returncode,wall_seconds=time.monotonic()-start),indent=2)+'\n')
sys.stdout.buffer.write(r.stdout);sys.stderr.buffer.write(r.stderr)
raise SystemExit(r.returncode)
