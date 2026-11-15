from pathlib import Path
import json,re,subprocess,time
r=Path('/home/ayates/trust-cg-soundness-20260914');first=r/'cg-adapter-target-abi-adapter-first/result.json'
while True:
 if first.exists():
  record=json.loads(first.read_text())
  if record.get('complete'):break
 time.sleep(5)
assert record['passed'],record
base=['cargo','test','--locked','--offline','--color','never','-j','2']
rows=[
 ('prepared-first',base+['-p','trust-cg-lower','--lib','prepared_owner_reuses_prerequisites_and_arch_specific_preflights','--','--nocapture','--test-threads=1']),
 ('strict-first',base+['-p','trust-cg-lower','--lib','strict_adapter_rejects_swift_aggregate_scalarization','--','--nocapture','--test-threads=1']),
 ('bindings-first',base+['-p','trust-cg-lower','--test','direct_call_binding','--test','function_address_binding','--test','abi_definition_refusals','--test','v41_codegen_license','--','--nocapture','--test-threads=1']),
 ('native-first',base+['-p','trust-cg-codegen','--test','e2e_aarch64_i128_narrow_call','--','--nocapture','--test-threads=1']),
]
completed=['adapter-first']
for label,command in rows:
 result=subprocess.run(['python3',str(r/'run-cg-adapter-target-abi-check-20260920.py'),label,*command])
 record=json.loads((r/('cg-adapter-target-abi-'+label)/'result.json').read_text())
 assert result.returncode==0 and record['passed'],label
 log=(r/('cg-adapter-target-abi-'+label)/'command.log').read_text()
 assert 'SKIP:' not in log and 'test result: ok.' in log,label
 if label=='native-first':assert 'I128_NARROW_ABI opt_levels=4 native_calls=384' in log
 completed.append(label)
(r/'cg-adapter-target-abi-targeted-complete.json').write_text(json.dumps(dict(passed=True,completed=completed),indent=2)+'\n')
