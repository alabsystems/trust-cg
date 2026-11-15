from pathlib import Path
import hashlib,json,os,re,subprocess
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917');out=r/'cg-const-references-quality';out.mkdir()
assert json.loads((r/'cg-const-references-final-tests-third/results.json').read_text())['passed']
assert json.loads((r/'cg-const-references-production-second/results.json').read_text())['passed']
env=os.environ.copy();env.update(PATH='/home/ayates/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='1.97.1')
commands=[('format',['bash','scripts/check_fmt.sh']),('backend-format',['rustfmt','--edition','2021','--check','crates/rustc-codegen-trust-cg/src/const_references.rs']),('diff',['git','diff','--check']),('staged-diff',['git','diff','--cached','--check'])]
rows=[]
for label,command in commands:
 result=subprocess.run(command,cwd=p,env=env,capture_output=True,text=True)
 (out/(label+'.log')).write_text(result.stdout+result.stderr);rows.append(dict(label=label,command=command,exit_code=result.returncode));(out/'results.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows[-1]),flush=True);result.check_returncode()
binaries=[]
for folder,log in [('cg-const-references-final-tests-third',n+'.log') for n in ['images','historical-bounds','global-images','native-layout','global-conversion','merge']]:
 source=r/folder/log;paths=re.findall(r'Running .* \((/[^\n)]+)\)',source.read_text());assert paths,(folder,log)
 for name in paths:
  binary=Path(name)
  with binary.open('rb') as stream:digest=hashlib.file_digest(stream,'sha256').hexdigest()
  binaries.append(dict(log=str(source),path=str(binary),sha256=digest,bytes=binary.stat().st_size))
(out/'binaries.json').write_text(json.dumps(binaries,indent=2)+'\n')
(out/'qualified-tree.json').write_text(json.dumps(dict(head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip(),tree=subprocess.check_output(['git','write-tree'],cwd=p,text=True).strip()),indent=2)+'\n')

tools=[]
paths=['/usr/bin/python3','/usr/bin/cc','/usr/bin/as','/usr/bin/ld','/usr/bin/readelf','/usr/bin/git','/home/ayates/.rustup/toolchains/1.97.1-aarch64-unknown-linux-gnu/bin/rustc','/home/ayates/.rustup/toolchains/1.97.1-aarch64-unknown-linux-gnu/bin/cargo','/home/ayates/.rustup/toolchains/1.97.1-aarch64-unknown-linux-gnu/bin/rustfmt','/home/ayates/ay-pblendvb-repair-20260914/scripts/_oom_guard.py']
for name in paths:
 binary=Path(name).resolve()
 tools.append(dict(path=name,resolved=str(binary),sha256=hashlib.file_digest(binary.open('rb'),'sha256').hexdigest(),bytes=binary.stat().st_size))
(out/'tools.json').write_text(json.dumps(tools,indent=2)+'\n')
