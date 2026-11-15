from pathlib import Path
import json,hashlib,subprocess,time,sys,os
p=Path('$HOME/trust-cg/target/indirect-unwind-investigation');exec((p/'env.py').read_text())
label=sys.argv[1];backend=Path(sys.argv[2]).resolve();r=json.loads((p/(label+'-results.json')).read_text());assert r['returncode']==0 and not r['timed_out']
deps=p/label/'target/aarch64-unknown-linux-gnu/debug/deps'
sysroot=p/(label+'-dynamic-sysroot');libdir=sysroot/'lib/rustlib/aarch64-unknown-linux-gnu/lib';libdir.mkdir(parents=True,exist_ok=True)
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
libs=[]
for src in sorted(deps.iterdir()):
 if src.suffix not in ['.rlib','.so']:continue
 dest=libdir/src.name
 if not dest.exists():dest.symlink_to(src)
 assert dest.resolve()==src.resolve()
 libs.append(dict(name=src.name,source=str(src),sha256=sha(src)))
assert any(x['name']=='libstd.so' for x in libs)
(p/(label+'-dynamic-sysroot.json')).write_text(json.dumps(libs,indent=2)+'\n')
rows=[]
def run(d,step,cmd,native=False):
 start=time.monotonic();e=env.copy()
 if native:e.update(LD_LIBRARY_PATH=str(libdir)+':'+str(d)+':'+env['LD_LIBRARY_PATH'],LD_DEBUG='libs')
 with (d/(step+'.log')).open('wb') as log:r=subprocess.run(cmd,env=e,stdout=log,stderr=subprocess.STDOUT,timeout=240)
 rows.append(dict(directory=str(d),step=step,command=cmd,returncode=r.returncode,wall_seconds=time.monotonic()-start,environment={k:e[k] for k in ['LD_LIBRARY_PATH','LD_DEBUG'] if k in e}));(p/(label+'-dynamic-results.json')).write_text(json.dumps(rows,indent=2)+'\n');print(d.name,step,r.returncode,flush=True);return r.returncode
for lane in ['llvm','cg']:
 d=p/(label+'-dynamic-'+lane);d.mkdir(exist_ok=True)
 cmd=[str(tc/'bin/trustc'),'--sysroot',str(sysroot),'--edition=2024','--crate-name=core_consumer','--crate-type=cdylib','-Cprefer-dynamic','-Cpanic=unwind','-Copt-level=0','-Ccodegen-units=1','-Ztrust-verify=off',str(p/'core-consumer.rs'),'-o',str(d/'libconsumer.so')]
 if lane=='cg':cmd+=['-Zcodegen-backend='+str(backend),'-Ztrust-ir-cg-args=diag-json no-proof-certs']
 if run(d,'compile',cmd):continue
 if run(d,'link',['cc','-O2',str(p/'core-driver.c'),'-L'+str(d),'-lconsumer','-Wl,-rpath-link,'+str(libdir),'-Wl,-rpath,'+str(d),'-Wl,-rpath,'+str(libdir),'-o',str(d/'native.elf')]):continue
 run(d,'consumer-elf',['readelf','-Wds',str(d/'libconsumer.so')]);run(d,'driver-elf',['readelf','-Wd',str(d/'native.elf')]);run(d,'native',[str(d/'native.elf')],True)
for name in ['real-runtime','mixed-core-panic','core-reference-format']:
 d=p/(label+'-dynamic-'+name);d.mkdir(exist_ok=True)
 cmd=[str(tc/'bin/trustc'),'--sysroot',str(sysroot),'--edition=2024','-Cprefer-dynamic','-Cpanic=unwind','-Copt-level=0','-Ccodegen-units=1','-Ztrust-verify=off',str(p/(name+'.rs')),'-o',str(d/'native.elf')]
 if run(d,'compile',cmd):continue
 run(d,'driver-elf',['readelf','-Wd',str(d/'native.elf')]);run(d,'native',[str(d/'native.elf')],True)
d=p/(label+'-dynamic-library');d.mkdir(exist_ok=True);run(d,'readelf',['readelf','-Wds',str(libdir/'libstd.so')]);run(d,'relocations',['readelf','-Wr',str(libdir/'libstd.so')])
assert all(sha(Path(x['source']))==x['sha256'] for x in libs)

raise SystemExit(0 if all(x["returncode"] == 0 for x in rows) else 1)
