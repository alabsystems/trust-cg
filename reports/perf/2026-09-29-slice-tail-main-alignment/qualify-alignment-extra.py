from pathlib import Path
import subprocess,json,shutil,hashlib,time,re
p=Path('$HOME/trust-cg/target/slice-from-end-investigation');root=p.parents[1]
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
cmd=['python3',str(p/'workspace-online.py'),'test','-p','trust-cg-verify','--test','fsym_ub_map','--no-run','--message-format=json']
with (p/'root-extra-build.log').open('wb') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=1200)
assert r.returncode==0,r.returncode
events=[]
for line in (p/'root-extra-build.log').read_text().splitlines():
    try:events.append(json.loads(line))
    except ValueError:pass
assert any(e.get('reason')=='build-finished' and e['success'] for e in events)
a=[e for e in events if e.get('reason')=='compiler-artifact' and e.get('target',{}).get('name')=='fsym_ub_map' and e.get('executable')];assert len(a)==1
src=Path(a[0]['executable']);dst=p/'fsym_ub_map-merged-2.test';shutil.copy2(src,dst)
(p/'root-extra-build-receipt.json').write_text(json.dumps(dict(command=cmd,original_path=str(src),immutable_path=str(dst),sha256=sha(dst)),indent=2)+'\n')
exec((p/'env.py').read_text());env['XDG_CACHE_HOME']='/tmp/trust-cg-borrowed-aggregate-proof-qjyzzw76'
rows=[]
for label,exe,filter,overlay in [('ub-map',dst,'',{}),('cse-opt-in',p/'trust-cg-opt-trust_cg_opt-merged-2.test','x86_cse_keeps_a_duplicate_whose_',{'TCG_X86_CSE_LOAD_TRANSPARENT':'1'})]:
    cmd=[str(exe),filter,'--nocapture','--test-threads=1'];log=p/f'root-extra-{label}.log';start=time.monotonic()
    with log.open('wb') as f:r=subprocess.run(cmd,env=env|overlay,stdout=f,stderr=subprocess.STDOUT,timeout=300)
    rows.append(dict(command=cmd,log=str(log),returncode=r.returncode,environment_overlay=overlay,wall_seconds=time.monotonic()-start,sha256=sha(exe)))
    (p/'root-extra-results.json').write_text(json.dumps(rows,indent=2)+'\n')
    assert r.returncode==0 and re.search(r'running [1-9][0-9]* tests?',log.read_text()),label
    print(label,r.returncode,flush=True)
