from pathlib import Path
import json,os,subprocess,time
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917');out=r/'cg-pointer-casts-quality-final';out.mkdir()
assert json.loads((r/'cg-pointer-casts-native-first/results.json').read_text())['expected_results_observed']
env=os.environ.copy();env['PATH']='/home/ayates/.cargo/bin:'+env.get('PATH','');env['RUSTUP_TOOLCHAIN']='1.97.1'
rows=[]
for name,cmd in [
 ('fmt',['bash','scripts/check_fmt.sh']),
 ('new-helper-fmt',['rustup','run','1.97.1','rustfmt','--edition','2021','--check','crates/rustc-codegen-trust-cg/src/pointer_casts.rs','crates/rustc-codegen-trust-cg/src/canonicalize_copies.rs']),
 ('diagnostics',['python3','scripts/generate_diagnostics_inventory.py','--write']),
 ('docs-write',['python3','scripts/check_documentation.py','--write']),
 ('docs-check',['python3','scripts/check_documentation.py','--check']),
 ('diff',['git','diff','--check'])]:
 start=time.monotonic();result=subprocess.run(cmd,cwd=p,env=env,capture_output=True,text=True);(out/(name+'.log')).write_text(result.stdout+result.stderr)
 row=dict(name=name,command=cmd,exit_code=result.returncode,seconds=time.monotonic()-start);rows.append(row);(out/'results.json').write_text(json.dumps(dict(passed=all(x['exit_code']==0 for x in rows),results=rows),indent=2)+'\n');print(json.dumps(row),flush=True);result.check_returncode()
