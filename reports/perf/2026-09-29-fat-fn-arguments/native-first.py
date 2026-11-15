from pathlib import Path
import subprocess,json,time
p=Path('$HOME/trust-cg/target/fat-fn-spread-investigation');rows=[]
for label,filter in [
 ('fat-fn','residual_conversion::no_proof_fat_fn'),
 ('virtual','residual_conversion::no_proof_virtual'),
 ('closure','closure_wrappers::no_proof_closure_wrappers_match_llvm')]:
 cmd=['python3',str(p/'runtime-first.py'),filter];log=p/f'native-{label}-first.log';start=time.monotonic()
 with log.open('wb') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=1800)
 rows.append(dict(command=cmd,log=str(log),returncode=r.returncode,wall_seconds=time.monotonic()-start));(p/'native-first-results.json').write_text(json.dumps(rows,indent=2)+'\n');print(label,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
