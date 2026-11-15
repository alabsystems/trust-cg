from pathlib import Path
import subprocess,json,time
p=Path('$HOME/trust-cg/target/virtual-unwind-investigation');rows=[]
for label,filter in [
 ('virtual','residual_conversion::no_proof_virtual'),
 ('indirect','residual_conversion::no_proof_indirect_'),
 ('dyn-drop','residual_conversion::no_proof_dyn_drop_unwind'),
 ('terminate','terminate_pad::no_proof_terminate_pads_match_llvm')]:
 cmd=['python3',str(p/'runtime-third.py'),filter];log=p/f'native-{label}-third.log';start=time.monotonic()
 with log.open('wb') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=1800)
 rows.append(dict(command=cmd,log=str(log),returncode=r.returncode,wall_seconds=time.monotonic()-start));(p/'native-third-results.json').write_text(json.dumps(rows,indent=2)+'\n');print(label,r.returncode,flush=True)
raise SystemExit(0 if all(x['returncode']==0 for x in rows) else 1)
