from pathlib import Path
import subprocess,json,shutil,hashlib
p=Path('$HOME/trust-cg/target/slice-from-end-investigation');root=p.parents[1]
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
files=[Path(x) for x in subprocess.check_output(['git','ls-files'],cwd=root,text=True).splitlines() if (root/x).is_file() and x.endswith(('.rs','.toml','.lock'))]
(p/'root-merged-3-inputs.json').write_text(json.dumps({str(f):sha(root/f) for f in files},indent=2)+'\n')
cmd=['python3',str(root/'target/pointer-bytes-investigation/workspace-build.py'),'test','-p','trust-cg-verify','--lib','--test','soundness_manifest','--no-run','--message-format=json']
with (p/'root-build-merged-3.log').open('wb') as log:r=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=1200)
assert r.returncode==0,r.returncode
es=[]
for line in (p/'root-build-merged-3.log').read_text().splitlines():
 try:es.append(json.loads(line))
 except ValueError:pass
assert any(e.get('reason')=='build-finished' and e['success'] for e in es)
rows=[]
for name in ['trust_cg_verify','soundness_manifest']:
 a=[x for x in es if x.get('reason')=='compiler-artifact' and x.get('target',{}).get('name')==name and x.get('executable')];assert len(a)==1
 src=Path(a[0]['executable']);dst=p/f'{name}-merged-3.test';shutil.copy2(src,dst)
 rows.append(dict(command=cmd,original_path=str(src),immutable_path=str(dst),sha256=sha(dst)))
(p/'root-build-merged-3-receipt.json').write_text(json.dumps(rows,indent=2)+'\n');print('root built',flush=True)
exec((p/'env.py').read_text());env['XDG_CACHE_HOME']='/tmp/trust-cg-borrowed-aggregate-proof-qjyzzw76'
rows=[]
for label,name,filter in [
 ('x86-body','trust_cg_verify','x86_source_bound_body::'),
 ('x86-verifier','trust_cg_verify','x86_64_function_verifier::tests::'),
 ('loop-symexec','trust_cg_verify','loop_backedge_symexec::tests::'),
 ('fp-lowering','trust_cg_verify','fp_bv_lowering::tests::'),
 ('aarch64-affine','trust_cg_verify','aarch64_affine_values::tests::'),
 ('diag','trust_cg_verify','diag::tests::'),
 ('soundness-manifest','soundness_manifest','')]:
 dst=p/f'{name}-merged-3.test';cmd=[str(dst),filter,'--nocapture','--test-threads=1']
 with (p/f'root-{label}-merged-3.log').open('wb') as log:r=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=300)
 rows.append(dict(command=cmd,log=str(p/f'root-{label}-merged-3.log'),returncode=r.returncode,sha256=sha(dst)))
 (p/'root-merged-3-results.json').write_text(json.dumps(rows,indent=2)+'\n');print(name,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
