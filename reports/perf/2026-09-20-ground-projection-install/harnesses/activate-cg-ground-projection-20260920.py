# Resume activation after the standalone floor, whose first nested launch
# correctly refused the still-live installer's exclusive resource lease.
from pathlib import Path
import hashlib,json,os,shlex,shutil,subprocess
r=Path('/home/ayates/trust-cg-soundness-20260914')
prefix=Path('/home/ayates/.local')
source=Path('/home/ayates/trust-cg-abi-target-20260920')
out=r/'installed-ground-projection-first'
assert not (out/'identity.json').exists()
record=json.loads((out/'preflight-identity.json').read_text())
workspace_head=record['workspace_head']
destination=Path(record['directory'])
launcher=prefix/'bin/trust-cg'
previous=json.loads((r/'installed-adapter-abi-first/identity.json').read_text())
backend_target=Path(record['private_backend']['path'])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert len(record['preflight'])==246 and all(x['exit_code']==0 for x in record['preflight'])
assert record['solver_qualification']['passed'] and record['solver_units']['passed']
assert sha(launcher)==previous['launcher']['sha256']
for name in ['ay','clean']:
 path=prefix/'bin'/name
 assert path.is_symlink() and os.readlink(path)==str(Path(previous['directory'])/name)
floor=json.loads((r/'cg-ground-projection-floor-first/results.json').read_text())
assert floor['complete'] and floor['passed'] and len(floor['targets'])==129
record['floor_qualification']=floor
print('PASS complete required Linux floor against staged runtime',flush=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip()==workspace_head
assert not subprocess.check_output(['git','status','--porcelain'],cwd=source)
for row in record['tools']:assert sha(Path(row['executable']))==row['sha256']
assert sha(backend_target)==record['private_backend']['sha256']
shutil.copyfile(launcher, out/'previous-trust-cg')
script = '#!/bin/sh\n# Local development cohort; see '+str(destination/'identity.json')+'\n'
script += 'PATH='+shlex.quote(str(destination/'bin'))+':"${PATH:-/usr/bin:/bin}"\nexport PATH\n'
script += 'exec '+shlex.quote(str(destination/'trust-cg'))+' "$@"\n'
temporary = launcher.with_name('.trust-cg-ground-projection-'+str(os.getpid()))
temporary.write_text(script); temporary.chmod(0o755)
subprocess.run(['sh','-n',str(temporary)],check=True)
assert sha(launcher) == previous['launcher']['sha256']
os.replace(temporary,launcher)
record['links'] = []
for name in ['ay','clean']:
    path = prefix/'bin'/name
    assert path.is_symlink() and os.readlink(path) == str(Path(previous['directory'])/name)
    temporary = path.with_name('.'+name+'-ground-projection-'+str(os.getpid()))
    temporary.symlink_to(destination/name); os.replace(temporary,path)
    record['links'].append({'path':str(path),'target':os.readlink(path)})
record['launcher'] = {'path':str(launcher),'sha256':sha(launcher),'preserves_explicit_environment_overrides':True,'tool_discovery':'package prefix on PATH; no injected TCG/AY controls'}
record['version'] = subprocess.check_output([str(launcher),'--version'],text=True).strip()
for path in [out/'identity.json',destination/'identity.json',destination/'PROVENANCE.json']:
    path.write_text(json.dumps(record,indent=2)+'\n')
(out/'trust-cg-launcher').write_text(script)
(destination/'README.md').write_text('Local development compiler, AY solver and Clean certificate checker. The compiler launcher places this development package prefix on PATH without injecting proof-policy overrides. Explicit caller overrides remain explicit. Source identities, hashes and native preflight commands are recorded in identity.json. The compiler and AY use stock Rust builds; Clean uses genuine Targo in its explicit unverified development lane; this is not a signed package or a fully Trust-verified build. The exact source-bound constant leaf exports independently replayed lowering evidence at all four optimization levels. The included Trust backend compiles the O0/O1 output writer and the qualified fixed-array bounds programs in the explicit development frontend lane with backend checks enabled. Canonical allocation references, declared tuple images and direct global-address leaves are included; nine reference-return functions pass at O0/O1 with native ABI/value checks. Adjacent single-use integer comparisons branch directly at every optimization level; dominated bounds stores pass at O0/O1. Production frame effects now follow the validated emitted layout. The masked unwind source passes O2/O3 after its panic block is eliminated. The complete Linux regression repair adds explicit signed/unsigned i128 saturation with valid helper arguments, canonical niche-enum retag refusal, and the retained frame envelope needed for proof-required identity JIT. Original and lowered modules now bind verification receipts and JIT cache identity. Supported scalar constant/copy/conditional leaf frames retain their checked envelope. Caller argument classification follows the selected AArch64 object ABI; prepared Darwin Swift aggregate rewrites reject target-ABI changes. Four release CLI tiers additionally pass 384 native C calls across the i128/narrow-argument boundary. The updated AY release preserves indexed operator identity in checked substitution and derives native Boolean projections from complete checked images. Default and self-check letleak publication now returns UNSAT; explicit artifact demand still refuses its incomplete external certificate. General CSet, real unwind frames and broader frame/proof gaps remain. Larger frames and unsupported formal domains remain refused.\n')
print(json.dumps({'directory':str(destination),'preflight_commands':len(record['preflight']),'version':record['version']}),flush=True)
