from pathlib import Path
import hashlib,json,os,signal,subprocess,sys,time
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917');out=r/('cg-zero-storage-native-'+sys.argv[1]);out.mkdir()
build=json.loads((r/'cg-zero-storage-backend-second/results.json').read_text());assert build['passed']
sealed=Path('/home/ayates/toolchains/trust-a62ae50d');backend=r/'cg-zero-storage-backend-second/librustc_codegen_trust_cg.so'
pack=Path(json.loads((r/'installed-aot-arithmetic-first/identity.json').read_text())['directory'])
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_')) and k not in ['RUSTC','RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_TARGET']}
env.update(PATH=str(r/'cg-output-memory-tools-first/bin')+':'+str(pack/'bin')+':'+str(sealed/'bin')+':/home/ayates/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='trust',RUST_TEST_THREADS='1',RUST_MIN_STACK='16777216',XDG_CACHE_HOME=str(out/'cache'))
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Zero-storage leaves: ordinary native compile and execution')
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip();assert head==build['source']; assert subprocess.check_output(['git','write-tree'],cwd=p,text=True).strip()==build['tested_tree']
record=dict(source=head,scope='Ordinary uninstrumented Trust backend, explicit unverified Rust frontend, backend proof checks enabled. Writer refusal is not successful compiler admission.',backend_sha256=hashlib.sha256(backend.read_bytes()).hexdigest(),resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,cases=[])
(out/'request.json').write_text(json.dumps(record,indent=2)+'\n')
def run(name,cmd,cwd,timeout=300):
 result=guard.run_captured(cmd,16384,timeout,label=name,env=env,cwd=cwd)
 (cwd/(name+'.log')).write_text(result.stdout+result.stderr)
 assert not(result.memout or result.timed_out or result.cancelled or result.stdout_truncated or result.stderr_truncated)
 return dict(command=cmd,exit_code=result.returncode,seconds=result.wall_sec,rss_breached=result.memout,guard_evidence=result.guard_evidence)
sources=sorted((r/'cg-pointer-cast-sources').glob('*.rs'))+[p/'crates/trust-cg-verify/tests/fixtures/output_memory_writer.rs']
for original in sources:
 for opt in [0,1]:
  name=original.stem+'-O'+str(opt);folder=out/name;folder.mkdir();src=folder/original.name;src.write_bytes(original.read_bytes())
  command=[str(sealed/'bin/trustc'),'--edition=2024','--crate-type=lib','--emit=obj','-Cpanic=abort','--target','aarch64-unknown-linux-gnu',f'-Copt-level={opt}','-Ztrust-verify=off','-Zcodegen-backend='+str(backend),str(src),'-o',str(folder/(name+'.o'))]
  case=dict(name=name,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),compile=run('compile',command,folder))
  objects=sorted(folder.glob('*.o'));case['objects']=[dict(path=str(f.relative_to(out)),bytes=f.stat().st_size,sha256=hashlib.sha256(f.read_bytes()).hexdigest()) for f in objects]
  if case['compile']['exit_code']==0:
   assert case['compile']['exit_code']==0 and len(objects)==1,case
   # Link the emitted object to a C driver using the actual C argument/result
   # carriers. No pointer reconstructed from arbitrary integers is dereferenced.
   function=original.stem
   if function=='output_memory_writer':
    declaration='extern void checked_output_memory_writer(uint64_t *, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);'
    body=r"""uint64_t arena[16], before[16], words[5], seed=0x123456789abcdefULL;
    for(unsigned row=0;row<257;++row) {
      for(unsigned i=0;i<16;++i) arena[i]=before[i]=0xa5a5a5a5a5a5a5a5ULL ^ (row*16+i);
      for(unsigned i=0;i<5;++i) {
        seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
        words[i] = row==0 ? 0 : row==1 ? UINT64_MAX : row==2 ? (1ULL << (i*13)) : seed;
      }
      unsigned start=1+row%8;
      checked_output_memory_writer(arena+start, words[0], words[1], words[2], words[3], words[4]);
      for(unsigned i=0;i<16;++i) {
        uint64_t expected=i>=start && i<start+5 ? words[i-start] : before[i];
        if(arena[i]!=expected) { fprintf(stderr,"writer mismatch row=%u slot=%u\n",row,i); return 1; }
      }
    }"""
   elif function=='cast_fat_to_int':
    declaration='struct Slice { const uint8_t *p; uintptr_t length; }; extern uintptr_t cast_fat_to_int(struct Slice);'
    body='uint8_t values[4]={0}; for(unsigned i=0;i<4;++i) if(cast_fat_to_int((struct Slice){values+i,4-i})!=(uintptr_t)(values+i)) return 1;'
   elif function in ['cast_int_to_const','cast_int_to_mut']:
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
   runner=folder/'runner.c';runner.write_text('#include <stdint.h>\n#include <stdio.h>\n'+declaration+'\nint main(void) { '+body+' puts("native checks PASS"); return 0; }\n')
   extra=[]
   if function=='output_memory_writer':
    asm=folder/'abi.S';asm.write_bytes((r/'cg-zero-storage-writer-abi.S').read_bytes());extra=[str(asm)]
   case['disassemble']=run('disassemble',['objdump','-dr',str(objects[0])],folder);assert case['disassemble']['exit_code']==0
   case['unwind']=run('unwind',['readelf','--debug-dump=frames',str(objects[0])],folder);assert case['unwind']['exit_code']==0
   disassembly=(folder/'disassemble.log').read_text()
   # The audited native functions must actually use the frameless path.
   import re
   assert not re.search(r'\b(?:sp|wsp|x29|w29|x30|w30)\b',disassembly),disassembly
   case['frameless_bytes_observed']=True
   case['link']=run('link',['cc','-std=c11','-Wall','-Wextra','-Werror',str(runner),str(objects[0]),*extra,'-o',str(folder/'runner')],folder);assert case['link']['exit_code']==0,case
   case['execution']=run('run',[str(folder/'runner')],folder);assert case['execution']['exit_code']==0,case
  else:
   assert case['compile']['exit_code']==1 and not objects,case
   log=(folder/'compile.log').read_text()
   if original.stem=='cast_int_to_ref':
    assert 'pointer/integer address transport IntToPtr: U64 -> Ref(U64)' in log
    case['expected_refusal_reason_observed']=True
   else:
    # Retain actual next proof gaps, without turning refusal into admission.
    assert 'TCG-PROOF-' in log,log
    case['remaining_proof_refusal']=True
  record['cases'].append(case);(out/'results.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(dict(name=name,exit_code=case['compile']['exit_code'],executed='execution' in case)),flush=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()==head
assert all('execution' in c or c.get('expected_refusal_reason_observed') or c.get('remaining_proof_refusal') for c in record['cases'])
record.update(complete=True,execution_cases=sum('execution' in c for c in record['cases']),scope='Ordinary uninstrumented Trust backend; explicit unverified development Rust frontend, backend proofs enabled. Successful native programs are linked against C controls; the output writer additionally checks all caller arena words and ABI callee-save registers. Refusals are retained. Finite regression evidence, not an end-to-end Rust proof.')
(out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
