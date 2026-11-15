from pathlib import Path
import dataclasses,hashlib,json,os,re,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');source=r/'cg-canonical-bounds-tests-second';out=r/'cg-canonical-bounds-oracle-first';out.mkdir()
report=json.loads((source/'results.json').read_text());assert report['passed']
directory=Path(re.search(r'CANONICAL_BOUNDS_NATIVE_DIR=([^\n]+)',(source/'native.log').read_text())[1]);(out/'oracle.c').write_bytes((directory/'oracle.c').read_bytes())
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Independent bounds trap oracle mutation controls')
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_'))}
record=dict(resources=plan._asdict(),commands=[],cases=[],complete=False,oracle_sha256=hashlib.sha256((out/'oracle.c').read_bytes()).hexdigest())
def save():(out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
def run(name,cmd):
 result=guard.run_captured(cmd,16384,120,label=name,env=env,cwd=out)
 row=dataclasses.asdict(result)
 for field in ['stdout','stderr']:(out/(name+'.'+field+'.log')).write_text(row.pop(field))
 row.update(name=name,command=cmd);record['commands'].append(row);save()
 assert not any([result.memout,result.timed_out,result.cancelled,result.stdout_truncated,result.stderr_truncated])
 return result.returncode
cases=[
 ('correct','cmp x0,#8\nb.lo 1f\nbrk #0\n1: str x0,[x1]\nret',0),
 ('missing-check','str x0,[x1]\nret',15),
 ('wrong-width','cmp w0,#8\nb.lo 1f\nbrk #0\n1: str x0,[x1]\nret',15),
 ('store-before-check','str x0,[x1]\ncmp x0,#8\nb.lo 1f\nbrk #0\n1: ret',16),
 ('missing-store','cmp x0,#8\nb.lo 1f\nbrk #0\n1: ret',12),
 ('off-by-one','cmp x0,#8\nb.ls 1f\nbrk #0\n1: str x0,[x1]\nret',15),
]
for name,body,expected in cases:
 assembly=out/(name+'.s');assembly.write_text('.text\n.global checked_index\n.type checked_index,%function\nchecked_index:\n'+body+'\n.size checked_index,.-checked_index\n.section .note.GNU-stack,"",@progbits\n');binary=out/name
 assert run(name+'-link',['cc','-std=c11','-Wall','-Wextra','-Werror','-DBOUND=8ULL',str(out/'oracle.c'),str(assembly),'-o',str(binary)])==0
 code=run(name+'-run',[str(binary)]);record['cases'].append(dict(name=name,exit_code=code,expected=expected,passed=code==expected));save();assert code==expected,(name,code,expected)
record.update(complete=True,passed=True,accepted=1,rejected=5);save();print(json.dumps(record['cases']),flush=True)
