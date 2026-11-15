from pathlib import Path
import json,subprocess,time
r=Path('/home/ayates/trust-cg-soundness-20260914')
record={'steps':[]}
out=r/'cg-adapter-abi-install-pipeline-first.json'
assert not out.exists()
start=time.monotonic()
while True:
    results=r/'cg-adapter-abi-production-first/results.json'
    if results.exists() and json.loads(results.read_text()).get('passed'):break
    log=(r/'cg-adapter-abi-production-first.log').read_text()
    assert 'Traceback (most recent call last)' not in log, log[-2000:]
    assert time.monotonic()-start<9000
    time.sleep(5)
for script,args in [
 ('qualify-cg-adapter-abi-bounds-native-20260920.py',[]),
 ('qualify-cg-adapter-abi-address-native-20260920.py',['first']),
 ('build-cg-adapter-abi-release-20260920.py',[]),
 ('install-cg-adapter-abi-20260920.py',[]),
 ('smoke-cg-adapter-abi-install-20260920.py',[]),
]:
    log=r/(script.removesuffix('.py')+'-first.log')
    assert not log.exists()
    print('START '+script,flush=True)
    with log.open('w') as stream:
        result=subprocess.run(['python3',str(r/script),*args],cwd=r,stdout=stream,stderr=subprocess.STDOUT)
    record['steps'].append(dict(script=script,log=str(log),exit_code=result.returncode))
    out.write_text(json.dumps(record,indent=2)+'\n')
    result.check_returncode()
    print('PASS '+script,flush=True)
record['passed']=True
out.write_text(json.dumps(record,indent=2)+'\n')
