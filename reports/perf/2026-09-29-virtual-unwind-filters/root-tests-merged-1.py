from pathlib import Path
import subprocess,json,hashlib,time
p=Path('$HOME/trust-cg/target/virtual-unwind-investigation');exec((p/'env.py').read_text());env['XDG_CACHE_HOME']='/tmp/trust-cg-borrowed-aggregate-proof-qjyzzw76'
rows=[]
for name,filters in [('rust_empty_filter',['']),('trust_ir_construct_inventory',['']),('fsym_ub_map',['']),('trust_cg_lower',['x86_64_isel::tests::']),('trust_cg_opt',['x86_dce::tests::']),('trust_cg_codegen',['exception_handling::tests::','eh_pipeline_tests::','module_merge::tests::']),('aarch64_elf_eh_relocation_inventory',['']),('e2e_aarch64_eh_typed',['']),('e2e_aarch64_eh_invoke_trust_ir',[''])]:
 for index,filter in enumerate(filters):
  exe=p/f'{name}-merged-1.test';log=p/f'root-{name}-{index}-merged-1.log';cmd=[str(exe),filter,'--nocapture','--test-threads=1'];start=time.monotonic()
  with log.open('wb') as f:r=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=600)
  rows.append(dict(command=cmd,log=str(log),returncode=r.returncode,wall_seconds=time.monotonic()-start,sha256=hashlib.sha256(exe.read_bytes()).hexdigest()));(p/'root-merged-1-results.json').write_text(json.dumps(rows,indent=2)+'\n');print(name,filter,r.returncode,flush=True)
raise SystemExit(0 if all(x['returncode']==0 for x in rows) else 1)
