from pathlib import Path
import dataclasses,hashlib,json,os,subprocess,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');out=r/'cg-live-frame-llvm-readers-first';out.mkdir();prefix=Path('/home/ayates/.local/lib/llvm-18-18.1.3-1ubuntu1');assert not prefix.exists()
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='User-local LLVM independent readers')
record=dict(package='llvm-18=1:18.1.3-1ubuntu1',package_sha256='1d9c87ff9fe17d0ee00703ec0f339ab687e2807b3508b51cf517e05281de104d',directory=str(prefix),resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,commands=[],tools=[])
def run(name,cmd):
 result=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(out/(name+'.log')),*map(str,cmd)],16384,600,label=name,env=dict(os.environ),cwd=out)
 record['commands'].append(dict(name=name,command=list(map(str,cmd)),**dataclasses.asdict(result)));(out/'results.json').write_text(json.dumps(record,indent=2)+'\n');assert not any([result.returncode,result.memout,result.timed_out,result.cancelled,result.stdout_truncated,result.stderr_truncated])
run('metadata',['apt-cache','show','llvm-18=1:18.1.3-1ubuntu1'])
run('download',['apt-get','download',record['package']])
packages=list(out.glob('*.deb'));assert len(packages)==1;package=packages[0];assert hashlib.sha256(package.read_bytes()).hexdigest()==record['package_sha256']
run('extract',['dpkg-deb','--extract',package,prefix])
for name in ['llvm-dwarfdump','llvm-readelf','llvm-objdump']:
 path=prefix/'usr/lib/llvm-18/bin'/name;assert path.is_file();run(name+'-version',[path,'--version']);run(name+'-libraries',['ldd',path])
 resolved=path.resolve();row=dict(name=name,path=str(path),resolved=str(resolved),sha256=hashlib.file_digest(resolved.open('rb'),'sha256').hexdigest(),bytes=resolved.stat().st_size)
 link=Path('/home/ayates/.local/bin')/name;assert not os.path.lexists(link);link.symlink_to(path);row['link']=str(link);record['tools'].append(row)
record['passed']=True;(out/'results.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record['tools']),flush=True)
