from pathlib import Path
import subprocess
p=Path('target/slice-from-end-investigation')
exec((p/'env.py').read_text())
for name,cmd in [
 ('docs-write',[ 'python3','scripts/check_documentation.py','--write','--targo',str(tc/'bin/targo')]),
 ('diagnostics-write',['python3','scripts/generate_diagnostics_inventory.py','--write']),
 ('native-matrix-write',['python3','scripts/native_test_host_matrix.py']),
 ('docs-check',['python3','scripts/check_documentation.py','--check','--targo',str(tc/'bin/targo')]),
 ('diagnostics-check',['python3','scripts/generate_diagnostics_inventory.py','--check'])]:
 with (p/('alignment-'+name+'.log')).open('wb') as f:run=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=300)
 print(name,run.returncode,flush=True)
 if run.returncode:raise SystemExit(run.returncode)
