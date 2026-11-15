from pathlib import Path
import subprocess,json,time
p=Path('target/indirect-unwind-investigation');rows=[]
cases=[('indirect','residual_conversion::no_proof_indirect_return_unwind_matches_llvm'),('dyn-drop','residual_conversion::no_proof_dyn_drop_unwind_matches_llvm'),('sret-negative','residual_conversion::no_proof_indirect_unwind_keeps_sret_refusal'),('terminate','terminate_pad::'),('direct-aggregate','residual_conversion::no_proof_aggregate_return_unwind_matches_llvm'),('associated-drop','associated_drop::'),('scalar-union','scalar_union_storage::'),('closure-storage','captured_closure_storage::')]
for name,filter in cases:
 c=['python3',str(p/'runtime-merged-1.py'),filter];start=time.monotonic()
 with (p/(name+'-merged-1.log')).open('wb') as log:r=subprocess.run(c,stdout=log,stderr=subprocess.STDOUT,timeout=600)
 rows.append(dict(name=name,command=c,returncode=r.returncode,wall_seconds=time.monotonic()-start));(p/'qualify-merged-1-results.json').write_text(json.dumps(rows,indent=2)+'\n');print(name,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
