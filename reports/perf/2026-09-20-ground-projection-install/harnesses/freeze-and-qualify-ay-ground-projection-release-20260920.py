from pathlib import Path
import dataclasses,hashlib,json,os,shutil,subprocess,sys,time

r=Path('/home/ayates/trust-cg-soundness-20260914')
export=Path('/home/ayates/ay-ground-projection-second-export-20260920')
result_path=r/'ay-shadow-ground-projection-release-first/result.json'
deadline=time.monotonic()+2400
while True:
    assert time.monotonic()<deadline,'release build did not finish'
    try:
        build=json.loads(result_path.read_text())
        if 'result' in build:
            assert build['complete'] and build['passed'] and build['inputs_unchanged'],build['result']
            break
    except (FileNotFoundError,json.JSONDecodeError):
        pass
    time.sleep(2)

def sha(path):
    digest=hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda:stream.read(1024*1024),b''):digest.update(chunk)
    return digest.hexdigest()

source=json.loads((export/'identity.json').read_text())
repo=Path('/home/ayates/ay-output-memory-repair-20260917')
assert not subprocess.check_output(['git','diff','--name-only',source['source_tree'],'--','crates','Cargo.toml','Cargo.lock','.cargo','rust-toolchain.toml','publish'],cwd=repo)
binary_dir=r/('ay-at-tree-'+source['source_tree'][:8]);binary_dir.mkdir()
binary=binary_dir/'ay';shutil.copy2('/home/ayates/ay-pblendvb-export-20260914/export/target/release/ay',binary)
identity=dict(source_commit='f23afa97aebcb218ac67d0a7057c51168fcd14a3',source_tree=source['source_tree'],source_export=source,
              binary=str(binary),sha256=sha(binary),build={k:v for k,v in build.items() if k!='before'},
              scope='Maintained stock Rust release CLI with checked indexed-symbol identity and native ground-substitution projection. Not a Trust-verified or signed release.')
(binary_dir/'identity.json').write_text(json.dumps(identity,indent=2)+'\n')
print('Frozen release',str(binary),identity['sha256'],flush=True)

sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
out=r/'ay-ground-projection-cli-first';out.mkdir()
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Native letleak publication release CLI qualification')
record=dict(identity=identity,resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,commands=[],complete=False,passed=False)
query=(r/'ay-letleak-self-check-diagnostic-first/query.smt2').read_bytes()
env={k:v for k,v in os.environ.items() if not k.startswith(('AY_','TCG_','TRUST_CG_'))}
for name,flags,expected in [('default',[],'unsat'),('self-check',['--self-check'],'unsat'),('explicit-proof',['--self-check'],'unknown')]:
    case=out/name;case.mkdir();(case/'query.smt2').write_bytes(query)
    if name=='explicit-proof':flags+=['--proof',str(case/'proof.alethe'),'--proof-format','alethe']
    command=[str(binary),'--memory','8192','--debug-cert',*flags,'-smt2',str(case/'query.smt2')]
    result=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(case/'command.log'),*command],16384,180,label=name,env=env,cwd=case)
    answers=[line for line in (case/'command.log').read_text().splitlines() if line in ['sat','unsat','unknown']]
    record['commands'].append(dict(name=name,command=command,query_sha256=sha(case/'query.smt2'),answers=answers,expected=expected,**dataclasses.asdict(result)))
    (out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
    print(name,answers,result.returncode,flush=True)
    assert not any([result.returncode,result.memout,result.timed_out,result.cancelled,result.stdout_truncated,result.stderr_truncated]),name
    assert answers==[expected],name
assert sha(binary)==identity['sha256']
record.update(complete=True,passed=True)
(out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
