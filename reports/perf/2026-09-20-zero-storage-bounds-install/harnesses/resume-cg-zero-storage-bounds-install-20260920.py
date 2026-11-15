from pathlib import Path
import hashlib,json,os,shlex,shutil,subprocess,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');source=Path('/home/ayates/trust-cg-output-byte-binding-20260917');prefix=Path('/home/ayates/.local');out=r/'installed-zero-storage-bounds-first'
record=json.loads((out/'results.json').read_text());assert len(record['preflight'])==181 and all(x['exit_code']==0 for x in record['preflight'])
assert not (out/'identity.json').exists()
build=json.loads((r/'cg-zero-storage-bounds-release-first/result.json').read_text());assert build['passed'];head=build['source']
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip()==head
assert not subprocess.check_output(['git','status','--porcelain'],cwd=source)
previous=json.loads((r/'installed-zero-storage-second/identity.json').read_text());destination=Path(record['directory']);launcher=prefix/'bin/trust-cg';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(launcher)==previous['launcher']['sha256']
for name in ['ay','clean']:assert os.readlink(prefix/'bin'/name)==str(Path(previous['directory'])/name)
for row in record['tools']:assert sha(Path(row['executable']))==row['sha256']
backend_target=Path(record['private_backend']['path']);assert sha(backend_target)==record['private_backend']['sha256']
native_record=json.loads((r/'cg-zero-storage-bounds-production-native-first/results.json').read_text());assert native_record['passed']
assert sha(backend_target)==native_record['production_backend']['sha256']
first=record['preflight'][-1]['command'];assert first[-3].endswith('/bounds_const-O0/bounds_const.rs') and first[-1].endswith('/bounds_const-O0/bounds_const-O0.o')
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Resume qualified bounds package native preflight')
(out/'resource-plan-resume.json').write_text(json.dumps(plan._asdict(),indent=2)+'\n')
def run(command,name,timeout=120):
 env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_'))};env['PATH']=str(destination/'bin')+':/usr/bin:/bin'
 result=guard.run_captured(command,16384,timeout,label=name,env=env,cwd=source)
 (out/(name+'.log')).write_text(result.stdout+result.stderr)
 row=dict(command=command,exit_code=result.returncode,seconds=result.wall_sec,guard_evidence=result.guard_evidence)
 record['preflight'].append(row);(out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
 print(json.dumps(dict(name=name,exit_code=result.returncode,seconds=result.wall_sec)),flush=True)
 assert not(result.returncode or result.memout or result.timed_out or result.cancelled or result.stdout_truncated or result.stderr_truncated),name
 return result.stdout
# Recompile every newly qualified Rust endpoint through the staged backend,
# require exact object bytes, then execute its arena and ABI oracle again.
assert any(case['name']=='output_memory_writer-O0' for case in native_record['cases'])
for case in native_record['cases']:
    name=case['name']; symbol,level=name.rsplit('-O',1)
    directory=out/name
    if name!='bounds_const-O0':directory.mkdir()
    source_file=directory/(symbol+'.rs')
    source_file.write_bytes((r/'cg-canonical-bounds-sources'/(symbol+'.rs')).read_bytes())
    obj=directory/(name+'.o')
    if name!='bounds_const-O0':run(['/home/ayates/toolchains/trust-a62ae50d/bin/trustc','--edition=2024','--crate-type=lib','--emit=obj','-Cpanic=abort','--target','aarch64-unknown-linux-gnu','-Copt-level='+level,'-Ztrust-verify=off','-Zcodegen-backend='+str(backend_target),str(source_file),'-o',str(obj)],name+'-compile')
    objects=list(directory.glob('*.o'));assert len(objects)==1, name
    obj=objects[0]
    assert sha(obj)==case['object_sha256'], name
    oracle=r/'cg-zero-storage-bounds-production-native-first'/name
    run(['cc','-std=c11','-Wall','-Wextra','-Werror',str(oracle/'runner.c'),str(oracle/'abi.S'),str(obj),'-o',str(directory/'runner')],name+'-link')
    assert run([str(directory/'runner')],name+'-execute').strip()=='native checks PASS'
assert len(record['preflight'])==180+3*len(native_record['cases'])
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
(destination/'README.md').write_text('Local development compiler, AY solver and Clean certificate checker. The compiler launcher places this development package prefix on PATH without injecting proof-policy overrides. Explicit caller overrides remain explicit. Source identities, hashes and native preflight commands are recorded in identity.json. The compiler and AY use stock Rust builds; Clean uses genuine Targo in its explicit unverified development lane; this is not a signed package or a fully Trust-verified build. The exact source-bound constant leaf exports independently replayed lowering evidence at all four optimization levels. The included Trust backend compiles the O0/O1 output writer and the qualified fixed-array bounds programs in the explicit development frontend lane with backend checks enabled. Conditional-comparison, unwind and broader frame/proof gaps remain. Larger frames and unsupported formal domains remain refused.\n')
print(json.dumps({'directory':str(destination),'preflight_commands':len(record['preflight']),'version':record['version']}),flush=True)
