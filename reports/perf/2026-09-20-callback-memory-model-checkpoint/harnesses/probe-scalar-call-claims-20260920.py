from pathlib import Path
import dataclasses,hashlib,json,os,re,sys
r=Path('/home/ayates/trust-cg-soundness-20260914')
source=r/'scalar-call-composition-claims'
manifest=json.loads((source/'manifest.json').read_text())
out=r/('scalar-call-composition-replay-'+sys.argv[1]);out.mkdir()
# Do not overlap this probe with the current heavy compiler qualification.
floor=json.loads((r/'cg-scalar-cell-floor-first/results.json').read_text())
assert floor['complete'] and floor['passed']
pack=Path(json.loads((r/'installed-floor-repair-first/identity.json').read_text())['directory'])
ay=pack/'bin/ay';clean=pack/'bin/clean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(ay)=='93fe897aea3b4ad5d2ff50c9729c8aa097bfcf36dcbf581e21c4515bbeaf400b'
assert sha(clean)=='680069f8d7185a8dbc0cc67e860d57a7df9ca4cf8bd8a4d8951346cbbf594dbc'
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Conditional opaque-call memory framing prototype')
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_'))}
record=dict(scope='Diagnostic per-conjunct isolation, not complete call composition. Standalone conditional single-call memory model. No compiler source/machine/byte binding or admission authority. External ABI private-byte preservation and noninterference remain explicit premises.',manifest=manifest,ay_sha256=sha(ay),clean_sha256=sha(clean),resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,commands=[],cases=[],complete=False)
def save():(out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
def run(name,cmd):
    log=out/(name+'.log')
    result=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(log),*cmd],16384,180,label=name,env=env,cwd=out)
    row=dataclasses.asdict(result);row.update(name=name,command=cmd)
    record['commands'].append(row);save()
    if any([result.memout,result.timed_out,result.cancelled,result.stdout_truncated,result.stderr_truncated]):raise RuntimeError('Incomplete resource-limited execution '+name)
    return result.returncode,log.read_text()
save()
for item in manifest['queries']:
    src=source/item['query'];assert sha(src)==item['sha256']
    query=out/src.name;query.write_bytes(src.read_bytes());name=query.stem
    proof=out/(name+'.alethe')
    cmd=[str(ay),'--memory','8192','-smt2',str(query)]
    if item['expected']=='unsat':cmd+=['--strict-proofs','--proof',str(proof),'--proof-format','alethe']
    code,log=run(name+'-ay',cmd)
    actual=[line for line in log.splitlines() if line in ['sat','unsat','unknown']]
    row=dict(name=name,expected=item['expected'],solver_exit=code,answers=actual,matched=code==0 and actual==[item['expected']],replayed=False,controls=[])
    record['cases'].append(row);save();print(json.dumps(row),flush=True)
    if not row['matched']:continue
    if item['expected']=='unsat':
        if not proof.is_file():continue
        packet=dict(type='alethe_certificate',version='1.0',problem=query.read_text(),proof=proof.read_text())
        cert=out/(name+'.json');cert.write_text(json.dumps(packet)+'\n')
        code,log=run(name+'-clean',[str(clean),'cert','verify-external',str(cert),'--verbose'])
        row['replayed']=code==0 and 'fully verified' in log
        if row['replayed']:
            for label,badproof in [('hole',re.sub(r':rule\s+[^\s)]+',':rule hole',packet['proof'],count=1)),('no-empty-clause',packet['proof'].replace('(cl)','(cl false)'))]:
                assert badproof!=packet['proof']
                bad=out/(name+'-'+label+'.json');bad.write_text(json.dumps(dict(packet,proof=badproof))+'\n')
                code,log=run(name+'-'+label,[str(clean),'cert','verify-external',str(bad),'--verbose'])
                row['controls'].append(dict(name=label,rejected=code==1 and 'fully verified' not in log))
            different_problem=(source/(name.split('-')[0]+'-private_write'+'.smt2')).read_text()
            bad=out/(name+'-changed-problem.json');bad.write_text(json.dumps(dict(packet,problem=different_problem))+'\n')
            code,log=run(name+'-changed-problem',[str(clean),'cert','verify-external',str(bad),'--verbose'])
            row['controls'].append(dict(name='changed-problem',rejected=code==1 and 'fully verified' not in log))
        save()
record.update(complete=True,passed=all(c['matched'] and (c['expected']=='sat' or c['replayed'] and len(c['controls'])==3 and all(x['rejected'] for x in c['controls'])) for c in record['cases']))
assert sha(ay)==record['ay_sha256'] and sha(clean)==record['clean_sha256'];save()
print(json.dumps(dict(complete=True,passed=record['passed'],cases=len(record['cases']))),flush=True)
sys.exit(0 if record['passed'] else 1)
