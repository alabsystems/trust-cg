from pathlib import Path
import hashlib,json,subprocess,time
r=Path('/home/ayates/trust-cg-soundness-20260914');b=Path('/home/ayates/trust-cg-output-byte-binding-20260917')
while True:
 p=r/'cg-module-receipt-floor-second/results.json'
 if p.exists():
  record=json.loads(p.read_text())
  if record.get('complete') and 'finished' in record:break
 time.sleep(5)
assert record['passed']
assert not subprocess.check_output(['git','status','--porcelain'],cwd=b,text=True).strip()
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=b,text=True).strip()==record['provenance']['source_sha']
source=r/'adapter-target-abi-baseline-source/crates/trust-cg-lower/tests/aarch64_adapter_target_abi.rs'
p=b/'crates/trust-cg-lower/tests/aarch64_adapter_target_abi.rs';assert not p.exists();p.write_bytes(source.read_bytes())
try:
 cmd=['python3',str(r/'run-cg-adapter-target-abi-baseline-20260920.py'),'baseline-first','cargo','test','--locked','--offline','--color','never','-j','2','-p','trust-cg-lower','--test','aarch64_adapter_target_abi','--','--nocapture','--test-threads=1']
 result=subprocess.run(cmd)
 record=json.loads((r/'cg-adapter-target-abi-baseline-first/result.json').read_text())
 log=(r/'cg-adapter-target-abi-baseline-first/command.log').read_text()
 observed=(result.returncode==1 and record['complete'] and record['source_unchanged'] and record['execution']['returncode']==101 and 'test result: FAILED. 0 passed; 1 failed;' in log and 'left: I32' in log and 'right: I8' in log)
 (r/'cg-adapter-target-abi-baseline-observation.json').write_text(json.dumps(dict(expected_regression_observed=observed,runner_exit=result.returncode),indent=2)+'\n')
 print('EXPECTED BASELINE REGRESSION',observed,flush=True)
finally:
 assert p.read_bytes()==source.read_bytes()
 p.unlink()
