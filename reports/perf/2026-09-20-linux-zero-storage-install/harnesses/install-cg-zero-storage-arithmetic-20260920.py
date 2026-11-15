from pathlib import Path
import hashlib, json, os, shlex, shutil, subprocess

r = Path('/home/ayates/trust-cg-soundness-20260914')
prefix = Path('/home/ayates/.local')
source = Path('/home/ayates/trust-cg-output-byte-binding-20260917')
out = r/'installed-zero-storage-second'
out.mkdir(exist_ok=True)
assert not (out/'identity.json').exists()
build=json.loads((r/'cg-zero-storage-release-second/result.json').read_text())
assert build['passed'] and build['inputs_unchanged'] and not build['status_after']
head=build['source'];assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip()==head
assert not subprocess.check_output(['git','status','--porcelain'],cwd=source)
previous=json.loads((r/'installed-output-memory-first/identity.json').read_text())
destination=prefix/('lib/trust-cg/'+head[:8]+'-ay43f133d3-cleaned2a80d1')
launcher=prefix/'bin/trust-cg';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(launcher)==previous['launcher']['sha256']
for name in ['ay','clean']:
 path=prefix/'bin'/name;assert path.is_symlink() and os.readlink(path)==str(Path(previous['directory'])/name)
import sys,time
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Zero-storage compiler cohort installation preflight')
(out/'resource-plan.json').write_text(json.dumps(plan._asdict(),indent=2)+'\n')
tools=[]
for name,identity in [('trust-cg',r/('trust-cg-at-'+head[:8])/'identity.json'),('ay',r/'ay-at-tree-43f133d3/identity.json'),('clean',r/'clean-at-wide-bv-tree-ed2a80d1/identity.json')]:
 data=json.loads(identity.read_text());binary=identity.parent/name;expected=data.get('sha256',data.get('binary_sha256'));assert sha(binary)==expected,name
 tools.append(dict(name=name,binary=str(binary),identity=data,sha256=expected))
record=dict(scope='Locally qualified development CLI, same AY/Clean binaries as previous cohort; genuine Trust backend included separately. No verified frontend, signed release or self-host claim.',directory=str(destination),tools=tools,preflight=[])
assert not destination.exists();(destination/'bin').mkdir(parents=True)
for row in tools:
 target=destination/row['name'];shutil.copyfile(row['binary'],target);target.chmod(0o555);assert sha(target)==row['sha256'];row['executable']=str(target)
 if row['name'] in ['ay','clean']:
  parent=destination/'store'/row['name'];version='local-'+row['sha256'][:16];store=parent/version/'bin'/row['name'];store.parent.mkdir(parents=True)
  shutil.copyfile(target,store);store.chmod(0o555);(parent/'current').symlink_to(version,target_is_directory=True)
  (destination/'bin'/row['name']).symlink_to(Path('../store')/row['name']/'current/bin'/row['name'])
backend=r/'cg-zero-storage-backend-second/librustc_codegen_trust_cg.so';backend_target=destination/backend.name
backend_record=json.loads((r/'cg-zero-storage-backend-second/results.json').read_text());assert backend_record['passed']
assert sha(backend)==json.loads((r/'cg-zero-storage-native-second/results.json').read_text())['backend_sha256']
shutil.copyfile(backend,backend_target);backend_target.chmod(0o555);assert sha(backend_target)==sha(backend)
record['private_backend']=dict(path=str(backend_target),sha256=sha(backend_target),qualification=backend_record)
(destination/'PROVENANCE.json').write_text(json.dumps(record,indent=2)+'\n')
def run(command,name,timeout=120):
 env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_'))};env['PATH']=str(destination/'bin')+':/usr/bin:/bin'
 result=guard.run_captured(command,16384,timeout,label=name,env=env,cwd=source)
 (out/(name+'.log')).write_text(result.stdout+result.stderr)
 row=dict(command=command,exit_code=result.returncode,seconds=result.wall_sec,guard_evidence=result.guard_evidence)
 record['preflight'].append(row);(out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
 print(json.dumps(dict(name=name,exit_code=result.returncode,seconds=result.wall_sec)),flush=True)
 assert not(result.returncode or result.memout or result.timed_out or result.cancelled or result.stdout_truncated or result.stderr_truncated),name
 return result.stdout
compiler = str(destination/'trust-cg')
for opt in range(4):
    obj = out/f'return42-O{opt}.o'; exe = out/f'return42-O{opt}'
    run([compiler,'--format=text','--target','aarch64-unknown-linux-gnu',f'-O{opt}','-c','examples/return_42.trust_ir','--emit-proofs',str(out/f'proofs-O{opt}'),'-o',str(obj)], f'compile-O{opt}')
    run(['cc','examples/return_42.c',str(obj),'-o',str(exe)],f'link-O{opt}')
    assert run([str(exe)],f'run-O{opt}').strip() == '42'
# Exercise the candidate CLI's text parser, ELF output and native conditional selects.
from select_cohort_fixture import write_fixture
fixture, oracle = write_fixture(out)
for opt in range(4):
    obj=out/f'select-O{opt}.o'; exe=out/f'select-O{opt}'
    run([compiler,'--format=text','--target','aarch64-unknown-linux-gnu',f'-O{opt}','-c',str(fixture),'-o',str(obj)],f'select-compile-O{opt}')
    run(['cc','-O2','-std=c11','-Wall','-Wextra','-Werror',str(oracle),str(obj),'-o',str(exe)],f'select-link-O{opt}')
    assert run([str(exe)],f'select-run-O{opt}').strip()=='CLI_SELECT_NATIVE functions=20 checks=3840'
# Exercise the candidate CLI's text parser, ELF output and native conditional selects.
from diamond_cohort_fixture import write_fixture
fixture, oracle = write_fixture(out)
for opt in range(4):
    obj=out/f'diamond-O{opt}.o'; exe=out/f'diamond-O{opt}'
    run([compiler,'--format=text','--target','aarch64-unknown-linux-gnu',f'-O{opt}','-c',str(fixture),'-o',str(obj)],f'diamond-compile-O{opt}')
    run(['cc','-O2','-std=c11','-Wall','-Wextra','-Werror',str(oracle),str(obj),'-o',str(exe)],f'diamond-link-O{opt}')
    assert run([str(exe)],f'diamond-run-O{opt}').strip()=='CLI_DIAMOND_NATIVE functions=20 checks=3840'
# Required arithmetic proof exports must execute before launcher replacement.
from aot_arithmetic_fixture import write_fixtures
for fixture, oracle, case in write_fixtures(out / 'arithmetic'):
    for opt in range(4):
        name=f'arithmetic-{case}-O{opt}'; obj=out/(name+'.o'); exe=out/name
        run([compiler,'--format=text','--target','aarch64-unknown-linux-gnu',f'-O{opt}','-c',str(fixture),'--emit-proofs',str(out/(name+'-proofs')),'-o',str(obj)],name+'-compile')
        assert len(list((out/(name+'-proofs')).glob('*.lowering.json')))==1
        run(['cc','-O2','-std=c11','-Wall','-Wextra','-Werror',str(oracle),str(obj),'-o',str(exe)],name+'-link')
        assert run([str(exe)],name+'-execute').strip()=='ARITHMETIC_AOT_NATIVE calls=144'
assert len(record['preflight'])==180
writer_source=out/'output_memory_writer.rs';writer_source.write_bytes((source/'crates/trust-cg-verify/tests/fixtures/output_memory_writer.rs').read_bytes())
run(['/home/ayates/toolchains/trust-a62ae50d/bin/trustc','--edition=2024','--crate-type=lib','--emit=obj','-Cpanic=abort','--target','aarch64-unknown-linux-gnu','-Copt-level=1','-Ztrust-verify=off','-Zcodegen-backend='+str(backend_target),str(writer_source),'-o',str(out/'output_memory_writer.o')],'rust-writer-compile')
objects=sorted(out.glob('output_memory_writer*.o'));assert len(objects)==1
writer_oracle=r/'cg-zero-storage-native-second/output_memory_writer-O1'
run(['cc','-std=c11','-Wall','-Wextra','-Werror',str(writer_oracle/'runner.c'),str(writer_oracle/'abi.S'),str(objects[0]),'-o',str(out/'writer-runner')],'rust-writer-link')
assert run([str(out/'writer-runner')],'rust-writer-run').strip()=='native checks PASS'
assert len(record['preflight'])==183
shutil.copyfile(launcher, out/'previous-trust-cg')
script = '#!/bin/sh\n# Local development cohort; see '+str(destination/'identity.json')+'\n'
script += 'PATH='+shlex.quote(str(destination/'bin'))+':"${PATH:-/usr/bin:/bin}"\nexport PATH\n'
script += 'exec '+shlex.quote(str(destination/'trust-cg'))+' "$@"\n'
temporary = launcher.with_name('.trust-cg-zero-storage-'+str(os.getpid()))
temporary.write_text(script); temporary.chmod(0o755)
subprocess.run(['sh','-n',str(temporary)],check=True)
assert sha(launcher) == previous['launcher']['sha256']
os.replace(temporary,launcher)
record['links'] = []
for name in ['ay','clean']:
    path = prefix/'bin'/name
    assert path.is_symlink() and os.readlink(path) == str(Path(previous['directory'])/name)
    temporary = path.with_name('.'+name+'-zero-storage-'+str(os.getpid()))
    temporary.symlink_to(destination/name); os.replace(temporary,path)
    record['links'].append({'path':str(path),'target':os.readlink(path)})
record['launcher'] = {'path':str(launcher),'sha256':sha(launcher),'preserves_explicit_environment_overrides':True,'tool_discovery':'package prefix on PATH; no injected TCG/AY controls'}
record['version'] = subprocess.check_output([str(launcher),'--version'],text=True).strip()
for path in [out/'identity.json',destination/'identity.json']:
    path.write_text(json.dumps(record,indent=2)+'\n')
(out/'trust-cg-launcher').write_text(script)
(destination/'README.md').write_text('Local development compiler, AY solver and Clean certificate checker. The compiler launcher places this development package prefix on PATH without injecting proof-policy overrides. Explicit caller overrides remain explicit. Source identities, hashes and native preflight commands are recorded in identity.json. The compiler and AY use stock Rust builds; Clean uses genuine Targo in its explicit unverified development lane; this is not a signed package or a fully Trust-verified build. The exact source-bound constant leaf exports independently replayed lowering evidence at all four optimization levels. The included Trust backend compiles the O1 output writer in the explicit development frontend lane with backend checks enabled; O0 and fat-pointer frame refusals remain. Larger frames and unsupported formal domains remain refused.\n')
print(json.dumps({'directory':str(destination),'preflight_commands':len(record['preflight']),'version':record['version']}),flush=True)
