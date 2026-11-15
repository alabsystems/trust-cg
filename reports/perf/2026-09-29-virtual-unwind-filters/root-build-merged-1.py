from pathlib import Path
import subprocess,json,shutil,hashlib
root=Path('$HOME/trust-cg');p=root/'target/virtual-unwind-investigation'
rows=[]
for label,args,names in [
 ('lower',['test','-p','trust-cg-lower','--lib','--test','rust_empty_filter','--test','trust_ir_construct_inventory','--no-run','--message-format=json'],['trust_cg_lower','rust_empty_filter','trust_ir_construct_inventory']),
 ('opt',['test','-p','trust-cg-opt','--lib','--no-run','--message-format=json'],['trust_cg_opt']),
 ('verify',['test','-p','trust-cg-verify','--test','fsym_ub_map','--no-run','--message-format=json'],['fsym_ub_map']),
 ('codegen',['test','-p','trust-cg-codegen','--lib','--test','aarch64_elf_eh_relocation_inventory','--test','e2e_aarch64_eh_typed','--test','e2e_aarch64_eh_invoke_trust_ir','--no-run','--message-format=json'],['trust_cg_codegen','aarch64_elf_eh_relocation_inventory','e2e_aarch64_eh_typed','e2e_aarch64_eh_invoke_trust_ir'])]:
 cmd=['python3',str(root/'target/pointer-bytes-investigation/workspace-build.py'),*args]
 with (p/f'root-{label}-build-merged-1.log').open('wb') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=1200)
 assert r.returncode==0,(label,r.returncode)
 es=[]
 for line in (p/f'root-{label}-build-merged-1.log').read_text().splitlines():
  try:es.append(json.loads(line))
  except ValueError:pass
 for name in names:
  a=[x for x in es if x.get('reason')=='compiler-artifact' and x.get('target',{}).get('name')==name and x.get('executable')];assert len(a)==1,(name,a)
  src=Path(a[0]['executable']);dst=p/f'{name}-merged-1.test';shutil.copy2(src,dst)
  rows.append(dict(command=cmd,original_path=str(src),immutable_path=str(dst),sha256=hashlib.sha256(dst.read_bytes()).hexdigest()))
 (p/'root-build-merged-1-receipt.json').write_text(json.dumps(rows,indent=2)+'\n');print(label,'PASS',flush=True)
