from pathlib import Path
import subprocess,json,time
p=Path('$HOME/trust-cg/target/slice-from-end-investigation');rows=[]
for label,filter in [
 ('from-end','residual_conversion::no_proof_slice_tail_from_end'),
 ('slice-tail','slice_tail::no_proof_slice_tail_match_llvm'),
 ('fat-fn','residual_conversion::no_proof_fat_fn'),
 ('borrowed-slice','borrowed_slice::no_proof_borrowed_slice_matches_llvm'),
 ('dyn-tail','dyn_tail::no_proof_dyn_tail_matches_llvm')]:
 cmd=['python3',str(p/'runtime-merged.py'),filter];log=p/f'native-{label}-merged.log';start=time.monotonic()
 with log.open('wb') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=1800)
 rows.append(dict(command=cmd,log=str(log),returncode=r.returncode,wall_seconds=time.monotonic()-start));(p/'native-merged-results.json').write_text(json.dumps(rows,indent=2)+'\n');print(label,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
