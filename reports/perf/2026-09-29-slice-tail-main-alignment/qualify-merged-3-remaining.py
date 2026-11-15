from pathlib import Path
import subprocess,json,hashlib
p=Path('$HOME/trust-cg/target/slice-from-end-investigation')
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
exec((p/'env.py').read_text());env['XDG_CACHE_HOME']='/tmp/trust-cg-borrowed-aggregate-proof-qjyzzw76'
rows=[]
for label,name,filter in [
 ('x86-verifier','trust_cg_verify','x86_64_function_verifier::tests::'),
 ('loop-symexec','trust_cg_verify','loop_backedge_symexec::tests::'),
 ('fp-lowering','trust_cg_verify','fp_bv_lowering::tests::'),
 ('aarch64-affine','trust_cg_verify','aarch64_affine_values::tests::'),
 ('diag','trust_cg_verify','diag::tests::'),
 ('soundness-manifest','soundness_manifest','')]:
 dst=p/f'{name}-merged-3.test';cmd=[str(dst),filter,'--nocapture','--test-threads=1']
 with (p/f'root-{label}-merged-3.log').open('wb') as log:r=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=300)
 rows.append(dict(command=cmd,log=str(p/f'root-{label}-merged-3.log'),returncode=r.returncode,sha256=sha(dst)))
 (p/'root-merged-3-remaining-results.json').write_text(json.dumps(rows,indent=2)+'\n');print(name,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
