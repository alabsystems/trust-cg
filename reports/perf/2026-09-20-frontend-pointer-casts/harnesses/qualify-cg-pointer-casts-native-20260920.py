from pathlib import Path
import hashlib,json,os,signal,subprocess,sys,time
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917');out=r/('cg-pointer-casts-native-'+sys.argv[1]);out.mkdir()
build=json.loads((r/'cg-pointer-casts-backend-first/results.json').read_text());assert build['passed']
sealed=Path('/home/ayates/toolchains/trust-a62ae50d');backend=r/'cg-pointer-casts-backend-first/librustc_codegen_trust_cg.so'
pack=Path(json.loads((r/'installed-aot-arithmetic-first/identity.json').read_text())['directory'])
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_')) and k not in ['RUSTC','RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_TARGET']}
env.update(PATH=str(r/'cg-output-memory-tools-first/bin')+':'+str(pack/'bin')+':'+str(sealed/'bin')+':/home/ayates/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='trust',RUST_TEST_THREADS='1',RUST_MIN_STACK='16777216',XDG_CACHE_HOME=str(out/'cache'))
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Typed pointer casts: ordinary native compile and execution')
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip();assert head==build['source']
record=dict(source=head,scope='Ordinary uninstrumented Trust backend, explicit unverified Rust frontend, backend proof checks enabled. Writer refusal is not successful compiler admission.',backend_sha256=hashlib.sha256(backend.read_bytes()).hexdigest(),resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,cases=[])
(out/'request.json').write_text(json.dumps(record,indent=2)+'\n')
def run(name,cmd,cwd,timeout=300):
 start=time.monotonic()
 with (cwd/(name+'.log')).open('w') as log:
  proc=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);watch=guard.rss_watchdog(proc,16384,label=name,grace_mb=0)
  try:code=proc.wait(timeout=timeout)
  except BaseException:os.killpg(proc.pid,signal.SIGKILL);proc.wait();raise
  finally:watch.stop()
 row=dict(command=cmd,exit_code=code,seconds=time.monotonic()-start,rss_breached=watch.breached)
 assert not watch.breached
 return row
sources=sorted((r/'cg-pointer-cast-sources').glob('*.rs'))+[p/'crates/trust-cg-verify/tests/fixtures/output_memory_writer.rs']
for original in sources:
 for opt in [0,1]:
  name=original.stem+'-O'+str(opt);folder=out/name;folder.mkdir();src=folder/original.name;src.write_bytes(original.read_bytes())
  command=[str(sealed/'bin/trustc'),'--edition=2024','--crate-type=lib','--emit=obj','-Cpanic=abort','--target','aarch64-unknown-linux-gnu',f'-Copt-level={opt}','-Ztrust-verify=off','-Zcodegen-backend='+str(backend),str(src),'-o',str(folder/(name+'.o'))]
  case=dict(name=name,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),compile=run('compile',command,folder))
  objects=sorted(folder.glob('*.o'));case['objects']=[dict(path=str(f.relative_to(out)),bytes=f.stat().st_size,sha256=hashlib.sha256(f.read_bytes()).hexdigest()) for f in objects]
  if original.stem not in ['cast_int_to_ref','cast_fat_to_int','cast_ref_ordered','cast_ref_reordered','cast_nominal_reinterpret','output_memory_writer']:
   assert case['compile']['exit_code']==0 and len(objects)==1,case
   captured=next(row for row in json.loads((r/'cg-pointer-casts-capture-first/results.json').read_text())['cases'] if row['name']==name)
   assert captured['objects'][0]['sha256']==case['objects'][0]['sha256'],case
   case['object_identical_to_diagnostic_capture']=True
   # Link the emitted object to a C driver using the actual C argument/result
   # carriers. No pointer reconstructed from arbitrary integers is dereferenced.
   function=original.stem
   if function in ['cast_int_to_const','cast_int_to_mut']:
    integer='intptr_t' if function.endswith('_mut') else 'uintptr_t'
    result='uint8_t *' if function.endswith('_mut') else 'const uint64_t *'
    declaration=f'extern {result} {function}({integer});'
    body=f'uintptr_t words[]={{0,1,8,0x0123456789abcdefULL,0x7fffffffffffffffULL,0x8000000000000000ULL,UINTPTR_MAX}}; for(unsigned i=0;i<sizeof(words)/sizeof(words[0]);++i) if((uintptr_t){function}(({integer})words[i])!=words[i]) return 1;'
   elif function=='cast_raw_to_raw':
    declaration=f'extern uint8_t *{function}(const uint64_t *);'
    body=f'uint64_t values[4]={{0,1,2,3}}; for(unsigned i=0;i<4;++i) if((void *){function}(&values[i])!=(void *)&values[i]) return 1;'
   elif function=='cast_raw_to_int':
    declaration=f'extern intptr_t {function}(uint8_t *);'
    body=f'uint8_t values[4]={{0}}; for(unsigned i=0;i<4;++i) if((uintptr_t){function}(&values[i])!=(uintptr_t)&values[i]) return 1;'
   elif function in ['cast_ref_ordered','cast_nominal_reinterpret','cast_ref_reordered']:
    fields='uint64_t b; uint8_t a;' if function=='cast_ref_reordered' else 'uint8_t a; uint64_t b;'
    declaration=f'struct Input {{ {fields} }}; extern uintptr_t {function}(const struct Input *);'
    body=f'struct Input values[4]={{{{0}}}}; for(unsigned i=0;i<4;++i) if({function}(&values[i])!=(uintptr_t)&values[i]) return 1;'
   else:
    qualifier='' if function=='cast_refmut_scalar' else 'const '
    declaration=f'extern uintptr_t {function}({qualifier}uint64_t *);'
    body=f'uint64_t values[4]={{0,1,2,3}}; for(unsigned i=0;i<4;++i) if({function}(&values[i])!=(uintptr_t)&values[i]) return 1;'
   runner=folder/'runner.c';runner.write_text('#include <stdint.h>\n#include <stdio.h>\n'+declaration+'\nint main(void) { '+body+' puts("pointer identity PASS"); return 0; }\n')
   case['link']=run('link',['cc','-std=c11','-Wall','-Wextra','-Werror',str(runner),str(objects[0]),'-o',str(folder/'runner')],folder);assert case['link']['exit_code']==0,case
   case['execution']=run('run',[str(folder/'runner')],folder);assert case['execution']['exit_code']==0,case
  else:
   assert case['compile']['exit_code']==1 and not objects,case
   log=(folder/'compile.log').read_text()
   if original.stem=='cast_int_to_ref':assert 'pointer/integer address transport IntToPtr: U64 -> Ref(U64)' in log
   else:assert all(message in log for message in ['TCG-PROOF-465','StpPreIndex','LdpPostIndex'])
   case['expected_refusal_reason_observed']=True
  record['cases'].append(case);(out/'results.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(case),flush=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()==head
record.update(expected_results_observed=True,scope='Ordinary uninstrumented Trust backend; explicit unverified development Rust frontend, backend proofs enabled. Twelve scalar pointer-cast programs compiled and executed against C pointer identity checks; aggregate, fat-pointer, writer and integer-to-reference cases retained their explicitly checked refusals. Finite regression evidence, not an end-to-end Rust proof.')
(out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
