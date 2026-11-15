from pathlib import Path
import json,re,subprocess,time
r=Path('/home/ayates/trust-cg-soundness-20260914')
deadline=time.monotonic()+1800
while True:
 floor=json.loads((r/'cg-complete-callback-floor-first/results.json').read_text())
 if floor['complete']:
  assert floor['passed']
  if (r/'cg-complete-callback-floor-first/binaries.json').exists():break
 assert time.monotonic()<deadline,'Baseline regression floor did not complete'
 time.sleep(5)
time.sleep(2)
installed=json.loads((r/'installed-floor-repair-first/identity.json').read_text())
native_env=['env','TRUST_CG_RUN_EXTERNAL_CERT_TESTS=1']
for name in ['ay','clean']:
 item=next(t for t in installed['tools'] if t['name']==name)
 path=Path(installed['directory'])/'bin'/name
 native_env.extend([f'TCG_JIT_REQUEST_CACHE_{name.upper()}={path}',f'TCG_JIT_REQUEST_CACHE_{name.upper()}_SHA256={item["sha256"]}'])
def unit(package,filter):
 return ['cargo','test','--locked','--offline','--color','never','-j','2','-p',package,'--lib',filter,'--','--nocapture','--test-threads=1']
def integration(target):
 return ['cargo','test','--locked','--offline','--color','never','-j','2','-p','trust-cg-codegen','--test',target,'--','--nocapture','--test-threads=1']
cases=[
 ('source-first',unit('trust-cg-verify','function_source::tests::')),
 ('request-first',unit('trust-cg-verify','function_request::tests::')),
 ('jit-inputs-first',unit('trust-cg-codegen','jit::source_inputs::tests::')),
 ('cache-first',native_env+unit('trust-cg-codegen','jit_cert::jit_request_cache_tests::')),
 ('native-first',native_env+unit('trust-cg-codegen','compiler::jit_source_campaign::')),
 ('arithmetic-first',integration('jit_source_bound_arithmetic')),
 ('policy-first',integration('jit_fail_closed_proof_policy')),
 ('core-first',integration('core_jit_planning')),
 ('threads-first',integration('jit_cross_thread_execute_mode')),
 ('no-verify-first',['cargo','check','--locked','--offline','--color','never','-j','2','-p','trust-cg-codegen','--no-default-features']),
]
results=[]
for label,command in cases:
 print('RUN',label,flush=True)
 log=r/('cg-module-receipt-'+label+'-runner.log')
 with log.open('x') as stream:
  result=subprocess.run(['python3',str(r/'run-cg-module-receipt-check-20260920.py'),label,*command],cwd=r,stdout=stream,stderr=subprocess.STDOUT)
 assert result.returncode==0,(label,result.returncode)
 transcript=(r/('cg-module-receipt-'+label)/'command.log').read_text()
 if label!='no-verify-first':
  counts=re.findall(r'test result: ok\. (\d+) passed; (\d+) failed; (\d+) ignored;',transcript)
  assert len(counts)==1 and int(counts[0][0])>0 and counts[0][1:]==('0','0'),(label,counts)
  assert 'SKIP ' not in transcript,(label,'unexpected skipped campaign')
 else:counts=[]
 if label=='native-first':
  assert transcript.count('JIT_SOURCE_NATIVE_ACCEPTED mode=')==2
  assert 'JIT_SOURCE_MODULE_CACHE_BOUND changed_original_misses=2 unchanged_hits=2 restored_original_hits=2' in transcript
 results.append(dict(label=label,counts=counts,passed=True))
 (r/'cg-module-receipt-qualification-first.json').write_text(json.dumps(dict(complete=len(results)==len(cases),cases=results),indent=2)+'\n')
 print(json.dumps(results[-1]),flush=True)
