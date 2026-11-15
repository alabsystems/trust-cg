from pathlib import Path
import dataclasses,hashlib,json,os,shutil,subprocess,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');b=Path('/home/ayates/trust-cg-output-byte-binding-20260917');capture=r/'cg-frameless-output-capture-first';out=r/'cg-frameless-output-native-first';out.mkdir()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
record=json.loads((capture/'results.json').read_text());assert record['complete'] and record['observed']
module=capture/'output_memory_writer-O1.trust-ir.json';retained=b/'crates/trust-cg-verify/tests/fixtures/output_memory_writer-layout-O1.trust-ir.json'
assert json.loads(module.read_text())==json.loads(retained.read_text()),'fresh original TrustIR changed'
pack=Path(json.loads((r/'installed-zero-storage-second/identity.json').read_text())['directory']);backend=pack/'librustc_codegen_trust_cg.so';driver=Path('/home/ayates/toolchains/trust-a62ae50d/bin/trustc')
assert sha(backend)=='7209ab8b7f940106d0f97e24d279fa84a84a371f53a5eb65e083a5a6694185c0'
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_')) and k not in ['RUSTC','RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_TARGET']}
env.update(PATH=str(pack/'bin')+':'+str(driver.parent)+':/home/ayates/.cargo/bin:/usr/bin:/bin',RUST_MIN_STACK='16777216',XDG_CACHE_HOME=str(out/'cache'))
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Fresh production writer bytes and ABI oracle')
result=dict(source_module_sha256=sha(module),retained_module_sha256=sha(retained),source_json_equal=True,production_backend_sha256=sha(backend),diagnostic_backend=record['backend'],resources=plan._asdict(),commands=[],complete=False)
def save():(out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
def run(name,cmd):
 value=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(out/(name+'.log')),*map(str,cmd)],16384,300,label=name,env=env,cwd=out)
 row=dataclasses.asdict(value);row.update(name=name,command=list(map(str,cmd)));result['commands'].append(row);save()
 assert value.returncode==0 and not any([value.timed_out,value.memout,value.cancelled,value.stdout_truncated,value.stderr_truncated]),name
 return (out/(name+'.log')).read_text()
old=r/'cg-zero-storage-native-second/output_memory_writer-O1'
for name in ['output_memory_writer.rs','runner.c','abi.S']:shutil.copyfile(old/name,out/name)
run('production-compile',[driver,'--edition=2024','--crate-type=lib','--emit=obj','-Cpanic=abort','--target','aarch64-unknown-linux-gnu','-Copt-level=1','-Ztrust-verify=off','-Zcodegen-backend='+str(backend),out/'output_memory_writer.rs','-o',out/'output_memory_writer-O1.o'])
objects=list(out.glob('*.o'));assert len(objects)==1;obj=objects[0]
actual=list((capture/'output_memory_writer-O1').glob('*.o'));assert len(actual)==1
assert obj.read_bytes()==actual[0].read_bytes()==(old/obj.name).read_bytes(),'instrumentation or fresh compile changed actual ELF'
run('extract-text',['objcopy','-O','binary','--only-section=.text',obj,out/'writer.bin'])
fixture=b/'crates/trust-cg-verify/tests/fixtures/output_memory_writer-frameless-O1.aarch64.bin'
assert (out/'writer.bin').read_bytes()==fixture.read_bytes()
run('disassemble',['objdump','-dr',obj]);run('unwind',['readelf','--debug-dump=frames',obj]);run('symbols-relocations',['readelf','-sr',obj])
run('link',['cc','-std=c11','-Wall','-Wextra','-Werror',out/'runner.c',obj,out/'abi.S','-o',out/'runner'])
log=run('execute',[out/'runner']);assert 'PASS' in log,log
result.update(complete=True,passed=True,elf_identical_to_capture_and_qualified_native=True,elf_sha256=sha(obj),fixture_sha256=sha(fixture),text_bytes=fixture.stat().st_size,native_calls=257,arena_words=16,distinct_buffer_placements=8)
assert sha(backend)==result['production_backend_sha256'];save();print(json.dumps({k:v for k,v in result.items() if k!='commands'}),flush=True)
