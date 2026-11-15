from pathlib import Path
import subprocess,json,shutil,hashlib
p=Path('$HOME/trust-cg/target/fat-fn-spread-investigation');root=p.parents[1]
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
files=[Path(x) for x in subprocess.check_output(['git','ls-files'],cwd=root,text=True).splitlines() if (root/x).is_file() and x.endswith(('.rs','.toml','.lock'))]
(p/'root-merged-inputs.json').write_text(json.dumps({str(f):sha(root/f) for f in files},indent=2)+'\n')
cmd=['python3',str(root/'target/pointer-bytes-investigation/workspace-build.py'),'test','-p','trust-cg-opt','-p','trust-cg-codegen','--lib','--no-run','--message-format=json']
with (p/'root-build-merged.log').open('wb') as log:r=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=1200)
assert r.returncode==0,r.returncode
es=[]
for line in (p/'root-build-merged.log').read_text().splitlines():
 try:es.append(json.loads(line))
 except ValueError:pass
assert any(e.get('reason')=='build-finished' and e['success'] for e in es)
rows=[]
for name in ['trust_cg_opt','trust_cg_codegen']:
 a=[x for x in es if x.get('reason')=='compiler-artifact' and x.get('target',{}).get('name')==name and x.get('executable')];assert len(a)==1
 src=Path(a[0]['executable']);dst=p/f'{name}-merged.test';shutil.copy2(src,dst)
 rows.append(dict(command=cmd,original_path=str(src),immutable_path=str(dst),sha256=sha(dst)))
(p/'root-build-merged-receipt.json').write_text(json.dumps(rows,indent=2)+'\n');print('root built',flush=True)
exec((p/'env.py').read_text());env['XDG_CACHE_HOME']='/tmp/trust-cg-borrowed-aggregate-proof-qjyzzw76'
rows=[]
for label,name,filter in [('peephole','trust_cg_opt','x86_peephole::tests::'),('branch-layout','trust_cg_codegen','x86_64::pipeline::tests::branch_layout_fallthrough_isolated_policy'),('lea-writeback','trust_cg_codegen','x86_64::pipeline::tests::x86_lea_self_writeback_')]:
 dst=p/f'{name}-merged.test';cmd=[str(dst),filter,'--nocapture','--test-threads=1']
 with (p/f'root-{label}-merged.log').open('wb') as log:r=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=300)
 rows.append(dict(command=cmd,log=str(p/f'root-{label}-merged.log'),returncode=r.returncode,sha256=sha(dst)))
 (p/'root-merged-results.json').write_text(json.dumps(rows,indent=2)+'\n');print(name,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
