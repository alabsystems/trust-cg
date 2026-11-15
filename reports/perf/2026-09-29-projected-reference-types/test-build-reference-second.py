from pathlib import Path
import subprocess,json,shutil,hashlib
root=Path('$HOME/trust-cg');p=root/'target/std-completion-investigation'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
rows=[]
for label,args,name,artifact in [('native-build-reference-second',['test','--test','aarch64_c_fnabi_aggregate_linux','--no-run','--message-format=json'],'aarch64_c_fnabi_aggregate_linux','native-reference-second.test')]:
 cmd=['python3',str(root/'target/pointer-bytes-investigation/build.py'),*args]
 with (p/(label+'.log')).open('wb') as log:r=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=900)
 assert r.returncode==0,(label,r.returncode)
 es=[]
 for line in (p/(label+'.log')).read_text().splitlines():
  try:es.append(json.loads(line))
  except ValueError:pass
 assert any(e.get('reason')=='build-finished' and e['success'] for e in es)
 a=[e for e in es if e.get('reason')=='compiler-artifact' and e.get('target',{}).get('name')==name];assert len(a)==1
 src=Path(a[0]['executable'] if artifact.endswith('.test') else a[0]['filenames'][0]);shutil.copy2(src,p/artifact)
 rows.append(dict(command=cmd,log=label+'.log',original_path=str(src),immutable_path=str(p/artifact),sha256=sha(p/artifact)));print(label,rows[-1]['sha256'],flush=True)
 (p/'native-build-reference-second-receipt.json').write_text(json.dumps(rows,indent=2)+'\n')
