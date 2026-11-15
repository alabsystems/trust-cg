from pathlib import Path
import hashlib,json,subprocess
r=Path('/home/ayates/trust-cg-soundness-20260914');b=Path('/home/ayates/trust-cg-output-byte-binding-20260917');c=Path('/home/ayates/trust-cg-output-source-capture-20260917')
assert json.loads((r/'cg-const-references-final-tests-third/results.json').read_text())['passed']
assert subprocess.check_output(['git','status','--porcelain'],cwd=c)==b''
files=['crates/rustc-codegen-trust-cg/src/lib.rs','crates/rustc-codegen-trust-cg/src/const_references.rs','crates/trust-cg-codegen/src/compiler.rs']
for name in files:(c/name).write_bytes((b/name).read_bytes())
subprocess.run(['git','add','--',*files],cwd=c,check=True)
subprocess.run(['git','apply',str(r/'cg-const-references-instrumentation-final.patch')],cwd=c,check=True)
subprocess.run(['git','add','--','crates/rustc-codegen-trust-cg/Cargo.toml','crates/rustc-codegen-trust-cg/src/lib.rs'],cwd=c,check=True)
(r/'cg-const-references-capture-third-source.json').write_text(json.dumps({name:hashlib.sha256((c/name).read_bytes()).hexdigest() for name in files+['crates/rustc-codegen-trust-cg/Cargo.toml']},indent=2)+'\n')
(r/'cg-const-references-capture-third-source.patch').write_bytes(subprocess.check_output(['git','diff','--cached','--binary'],cwd=c))
