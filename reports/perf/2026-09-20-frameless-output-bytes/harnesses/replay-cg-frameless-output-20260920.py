from pathlib import Path
import dataclasses, hashlib, json, os, re, sys
r=Path('/home/ayates/trust-cg-soundness-20260914');source=r/'cg-frameless-output-tests-second';out=r/'cg-frameless-output-replay-first'
report=json.loads((source/'results.json').read_text());assert report['passed']
queries=json.loads((source/'frameless_typed_output_query.json').read_text());assert len(queries)==1
assert queries==json.loads((source/'frameless_output_query.json').read_text())
queries=sorted(set(queries));files=[source/'frameless_typed_output_query.json']
qualification=json.loads((r/'ay-output-full-range-cli-merged-second/results.json').read_text())
assert qualification['complete'] and qualification['all_memory_queries_checked'] and len(qualification['cases'])==11 and len(qualification['consumer_regressions'])==54 and all(x['passed'] for x in qualification['consumer_regressions'])
controls=json.loads((r/'ay-output-full-range-cli-merged-second-controls/results.json').read_text());assert controls['complete'] and controls['all_passed']
out.mkdir();ay=Path(qualification['binary']);clean=r/'clean-at-wide-bv-tree-ed2a80d1/clean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(ay)==qualification['binary_sha256']==controls['binary_sha256']
assert qualification['source_tree']=='aa3ec1437fea4cb8444af9a72790fc9f35b7b9cf'
assert sha(clean)=='680069f8d7185a8dbc0cc67e860d57a7df9ca4cf8bd8a4d8951346cbbf594dbc'
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Final-byte output-memory theorem and three independent certificate corruptions')
env=os.environ.copy()
for k in list(env):
 if k.startswith(('AY_','TCG_','TRUST_CG_')):env.pop(k)
record=dict(source_head=report['head'],held_inputs=report['results'][0]['inputs_unchanged'],query_files=[str(x.relative_to(source)) for x in files],ay=str(ay),ay_sha256=sha(ay),clean=str(clean),clean_sha256=sha(clean),resources=plan._asdict(),rows=[],cases=[],complete=False)
def save():(out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
def run(name,command,mb=8192):
 result=guard.run_captured(command,mb,180,label=name,env=env,cwd=out)
 row=dataclasses.asdict(result) if dataclasses.is_dataclass(result) else result._asdict()
 for field in ['stdout','stderr']:(out/(name+'.'+field+'.log')).write_text(row.pop(field))
 row.update(name=name,command=command);record['rows'].append(row);save()
 assert not any([result.timed_out,result.memout,result.cancelled,result.stdout_truncated,result.stderr_truncated]),name
 return result.returncode,result.stdout+result.stderr
for index,query in enumerate(queries):
 name=f'output-bytes-{index:02}';file=out/(name+'.smt2');file.write_text(query);proof=out/(name+'.alethe')
 code,log=run(name+'-ay',[str(ay),'--memory','8192','-smt2',str(file),'--strict-proofs','--proof',str(proof),'--proof-format','alethe'],16384)
 assert code==0 and 'unsat' in log.splitlines() and proof.is_file(),name
 cert=dict(type='alethe_certificate',version='1.0',problem=query,proof=proof.read_text())
 assert query.count('(assert ')==1
 start=query.index('(assert ')+8;depth=0;end=None
 for j in range(start,len(query)):
  if query[j]=='(':depth+=1
  elif query[j]==')':
   if depth==0:end=j;break
   depth-=1
 assert end is not None
 opposite=query[:start]+'(not '+query[start:end]+')'+query[end:]
 cases=[('original',cert,True),('hole',dict(cert,proof=re.sub(r':rule\s+[^\s)]+',':rule hole',cert['proof'],count=1)),False),('no-empty-clause',dict(cert,proof=cert['proof'].replace('(cl)','(cl false)')),False),('opposite-premise',dict(cert,problem=opposite),False)]
 for label,value,expected in cases:
  if not expected:assert value!=cert
  packet=out/(name+'-'+label+'.json');packet.write_text(json.dumps(value)+'\n')
  code,log=run(name+'-'+label,[str(clean),'cert','verify-external',str(packet),'--verbose'])
  accepted=code==0 and 'fully verified' in log
  row=dict(name=name,variant=label,certificate_sha256=sha(packet),accepted=accepted,expected=expected,passed=accepted==expected and code==(0 if expected else 1))
  record['cases'].append(row);save();assert row['passed'],row
 print(name,'PASS original and 3 mutations',flush=True)
record.update(complete=True,passed=len(record['cases'])==4 and all(x['passed'] for x in record['cases']),accepted=sum(x['accepted'] for x in record['cases']),rejected=sum(not x['accepted'] for x in record['cases']))
assert sha(ay)==record['ay_sha256'] and sha(clean)==record['clean_sha256'];save();print(json.dumps({k:v for k,v in record.items() if k not in ['rows','cases','source']}))
