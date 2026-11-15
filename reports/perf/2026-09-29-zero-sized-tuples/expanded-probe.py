from pathlib import Path
import subprocess,json,sys,time,hashlib
p=Path('$HOME/trust-cg/target/zst-tuple-investigation')
exec((p/'env.py').read_text())
backend=(p.parent/'reference-raw-reborrow-investigation/merged-1-backend.so').resolve()
label=sys.argv[1] if len(sys.argv)>1 else 'baseline'
if len(sys.argv)>2:backend=Path(sys.argv[2]).resolve()
rows=[]
def run(d,step,c):
 start=time.monotonic()
 with (d/(step+'.log')).open('wb') as f:r=subprocess.run(c,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=180)
 rows.append(dict(directory=str(d),step=step,command=c,returncode=r.returncode,wall_seconds=time.monotonic()-start,backend_sha256=hashlib.sha256(backend.read_bytes()).hexdigest()));(p/(label+'-results.json')).write_text(json.dumps(rows,indent=2)+'\n');print(d.name,step,r.returncode,flush=True);return r.returncode
for opt in [0,2]:
 for lane in ['llvm','cg']:
  d=p/f'{label}-{lane}-O{opt}';d.mkdir(exist_ok=True)
  c=[str(tc/'bin/trustc'),'--edition=2024','--crate-type=lib','--emit=obj,mir','-Cpanic=unwind','-Ccodegen-units=1','-Ztrust-verify=off',f'-Copt-level={opt}',str(p/'expanded-corpus.rs'),'--out-dir',str(d)]
  if lane=='cg':c+=['-Zcodegen-backend='+str(backend),'-Ztrust-ir-cg-args=diag-json no-proof-certs dump-trust-ir='+str(d/'ir')]
  if run(d,'compile',c):continue
  c=[str(tc/'bin/trustc'),'--edition=2024','-Cpanic=unwind','-Ztrust-verify=off',str(p/'expanded-driver.rs'),*['-Clink-arg='+str(f) for f in sorted(d.glob('*.o'))],'-o',str(d/'native.elf')]
  if run(d,'link',c):continue
  run(d,'native',[str(d/'native.elf')])
