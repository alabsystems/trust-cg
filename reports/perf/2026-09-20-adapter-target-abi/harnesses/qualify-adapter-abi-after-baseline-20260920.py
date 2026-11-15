from pathlib import Path
import json,subprocess,time
r=Path('/home/ayates/trust-cg-soundness-20260914')
while not (r/'cg-adapter-target-abi-baseline-observation.json').exists():time.sleep(5)
observed=json.loads((r/'cg-adapter-target-abi-baseline-observation.json').read_text());assert observed['expected_regression_observed'],observed
cmd=['python3',str(r/'run-cg-adapter-target-abi-check-20260920.py'),'adapter-first','cargo','test','--locked','--offline','--color','never','-j','2','-p','trust-cg-lower','--test','aarch64_adapter_target_abi','--','--nocapture','--test-threads=1']
raise SystemExit(subprocess.call(cmd))
