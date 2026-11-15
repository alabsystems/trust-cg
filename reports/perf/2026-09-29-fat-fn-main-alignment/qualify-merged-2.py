from pathlib import Path
import subprocess,json,shutil,hashlib,time
p=Path('$HOME/trust-cg/target/fat-fn-spread-investigation');root=p.parents[1]
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
files=[root/x for x in subprocess.check_output(['git','ls-files'],cwd=root,text=True).splitlines() if (root/x).is_file() and x.endswith(('.rs','.toml','.lock'))]
(p/'root-merged-2-inputs.json').write_text(json.dumps({str(f.relative_to(root)):sha(f) for f in files},indent=2)+'\n')
cmd=['python3',str(root/'target/pointer-bytes-investigation/workspace-build.py'),'test','-p','trust-cg-opt','-p','trust-cg-verify','-p','trust-cg-codegen','-p','trust-cg-cli','--lib','--test','aarch64_instruction_word_binding','--test','aarch64_instruction_word_formal','--test','emit_proofs_flag','--no-run','--message-format=json']
with (p/'root-build-merged-2.log').open('wb') as log:r=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=1200)
assert r.returncode==0,r.returncode
es=[]
for line in (p/'root-build-merged-2.log').read_text().splitlines():
 try:es.append(json.loads(line))
 except ValueError:pass
assert any(e.get('reason')=='build-finished' and e['success'] for e in es)
rows=[]
for name in ['trust_cg_opt','trust_cg_verify','trust_cg_codegen','aarch64_instruction_word_binding','aarch64_instruction_word_formal','emit_proofs_flag','trust-cg']:
 a=[x for x in es if x.get('reason')=='compiler-artifact' and x.get('target',{}).get('name')==name and x.get('executable')];assert len(a)==1,(name,a)
 src=Path(a[0]['executable']);dst=p/f'{name}-merged-2.test';shutil.copy2(src,dst)
 rows.append(dict(command=cmd,original_path=str(src),immutable_path=str(dst),sha256=sha(dst)))
(p/'root-build-merged-2-receipt.json').write_text(json.dumps(rows,indent=2)+'\n');print('root built',flush=True)
exec((p/'env.py').read_text());env['XDG_CACHE_HOME']='/tmp/trust-cg-borrowed-aggregate-proof-qjyzzw76'
rows=[]
for label,name,filter in [
 ('licm','trust_cg_opt','x86_licm::tests::'),
 ('word-proof','trust_cg_verify','aarch64_instruction_word_proofs::'),
 ('verifier','trust_cg_verify','function_verifier::tests::'),
 ('decode','trust_cg_codegen','aarch64::decode_check::tests::'),
 ('binding','aarch64_instruction_word_binding',''),
 ('formal-probe','aarch64_instruction_word_formal','every_probe_holds_in_process'),
 ('cli-proof','emit_proofs_flag','')]:
 dst=p/f'{name}-merged-2.test';cmd=[str(dst),filter,'--nocapture','--test-threads=1'];start=time.monotonic()
 with (p/f'root-{label}-merged-2.log').open('wb') as log:r=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=900)
 rows.append(dict(command=cmd,log=str(p/f'root-{label}-merged-2.log'),returncode=r.returncode,wall_seconds=time.monotonic()-start,sha256=sha(dst)))
 (p/'root-merged-2-results.json').write_text(json.dumps(rows,indent=2)+'\n');print(label,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
# The CLI harness embeds the original executable path; bind it after use too.
for row in json.loads((p/'root-build-merged-2-receipt.json').read_text()):
 if Path(row['original_path']).name=='trust-cg':assert sha(Path(row['original_path']))==row['sha256']
