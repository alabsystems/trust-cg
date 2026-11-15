from pathlib import Path
import subprocess
p=Path('target/virtual-unwind-investigation')
exec((p/'env.py').read_text())
for name,cmd in [
 ('docs-merged-2-write',[ 'python3','scripts/check_documentation.py','--write','--targo',str(tc/'bin/targo')]),
 ('diagnostics-merged-2-write',['python3','scripts/generate_diagnostics_inventory.py','--write']),
 ('native-matrix-merged-2-write',['python3','scripts/native_test_host_matrix.py']),
 ('docs-check-merged-2',['python3','scripts/check_documentation.py','--check','--targo',str(tc/'bin/targo')]),
 ('diagnostics-check-merged-2',['python3','scripts/generate_diagnostics_inventory.py','--check'])]:
 with (p/(name+'.log')).open('wb') as f:run=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=300)
 print(name,run.returncode,flush=True)
 if run.returncode:raise SystemExit(run.returncode)
