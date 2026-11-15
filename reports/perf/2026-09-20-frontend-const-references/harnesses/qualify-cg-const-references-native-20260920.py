from pathlib import Path
import dataclasses,hashlib,json,os,shutil,struct,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917');production=r/('cg-const-references-production-'+sys.argv[1]);out=r/('cg-const-references-native-'+sys.argv[1]);out.mkdir()
a=json.loads((production/'results.json').read_text());assert a['passed'] and a['complete']
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Actual frontend global image native oracle')
record=dict(production_backend=a['backend'],source=a['source'],resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,commands=[],cases=[])
env=dict(os.environ);env['PATH']='/usr/bin:/bin'
def save():(out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
def run(label,cmd,cwd):
 result=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(out/(label+'.log')),*map(str,cmd)],16384,300,label=label,env=env,cwd=cwd)
 row=dataclasses.asdict(result);row.update(name=label,command=list(map(str,cmd)));record['commands'].append(row);save()
 assert result.returncode==0 and not any([result.timed_out,result.memout,result.cancelled,result.stdout_truncated,result.stderr_truncated]),label
 return (out/(label+'.log')).read_text()
def elf_static_images(paths):
 symbols={};relocs=[]
 for path in paths:
  raw=path.read_bytes();assert raw[:6]==b'\x7fELF\x02\x01'
  assert struct.unpack_from('<H',raw,18)[0]==183
  off=struct.unpack_from('<Q',raw,40)[0];stride,count=struct.unpack_from('<HH',raw,58)
  sections=[struct.unpack_from('<IIQQQQIIQQ',raw,off+i*stride) for i in range(count)]
  by_index={}
  for index,section in enumerate(sections):
   if section[1]!=2:continue
   strings=sections[section[6]];names=raw[strings[4]:strings[4]+strings[5]]
   for i in range(section[5]//section[9]):
    n,info,other,shndx,value,size=struct.unpack_from('<IBBHQQ',raw,section[4]+i*section[9])
    name=names[n:names.find(b'\0',n)].decode();row=dict(name=name,section=(path.name,shndx),value=value,size=size)
    if 0<shndx<len(sections):
     slot=sections[shndx];row['bytes']=raw[slot[4]+value:slot[4]+value+size].hex();row['section_align']=slot[8]
    if shndx or name not in symbols:symbols[name]=row
    by_index[(index,i)]=row
  for section in sections:
   if section[1]!=4:continue
   for i in range(section[5]//section[9]):
    offset,info,addend=struct.unpack_from('<QQq',raw,section[4]+i*section[9])
    relocs.append(dict(section=(path.name,section[7]),offset=offset,type=info&0xffffffff,target=by_index[(section[6],info>>32)]['name'],addend=addend))
 expected={'IMAGE_BYTES':19,'IMAGE_MUT':8,'IMAGE_REF':8,'IMAGE_PACKED':11,'IMAGE_FN':8,'IMAGE_CYCLE':8}
 for name,size in expected.items():assert symbols[name]['size']==size,(name,symbols[name])
 assert bytes.fromhex(symbols['IMAGE_BYTES']['bytes'])==b'nineteen-byte-image'
 assert bytes.fromhex(symbols['IMAGE_MUT']['bytes'])==struct.pack('<Q',0x0123456789abcdef)
 for name in ['IMAGE_MUT','IMAGE_REF','IMAGE_FN','IMAGE_CYCLE']:
  assert symbols[name]['value']%8==0 and symbols[name]['section_align']>=8
 for name,offset in [('IMAGE_REF',0),('IMAGE_PACKED',1),('IMAGE_FN',0),('IMAGE_CYCLE',0)]:
  symbol=symbols[name];refs=[row for row in relocs if row['section']==symbol['section'] and symbol['value']<=row['offset']<symbol['value']+symbol['size']]
  assert len(refs)==1,(name,refs)
  ref=refs[0];assert ref['offset']==symbol['value']+offset and ref['type']==257 and ref['addend']==0,(name,ref)
  if name in ['IMAGE_REF','IMAGE_PACKED']:
   target=symbols[ref['target']];assert target['size']==5 and bytes.fromhex(target['bytes'])==b'hello',target
  else:assert ref['target']==('image_function' if name=='IMAGE_FN' else 'IMAGE_CYCLE')
 return dict(symbols=[symbols[n] for n in expected],relocations=relocs)
for case in a['cases']:
 name=case['name'];symbol=name.rsplit('-O',1)[0]
 if symbol in ['bounds_unwind','image_aligned','image_scalars']:
  assert not case['production_admitted'] and case['proof_refusal'];continue
 assert case['production_admitted'],case
 folder=out/name;folder.mkdir();originals=sorted((production/name).glob('*.o'));assert len(originals)==7
 objects=[]
 for original in originals:
  obj=folder/original.name;shutil.copyfile(original,obj);objects.append(obj)
 capture=json.loads((r/'cg-const-references-capture-third/results.json').read_text())
 previous=next(row for row in capture['cases'] if row['name']==name)
 assert [hashlib.sha256(obj.read_bytes()).hexdigest() for obj in objects]==[obj['sha256'] for obj in previous['objects']]
 fixture=r/('cg-const-references-static-oracle.c' if symbol=='image_statics' else 'cg-const-references-aligned-oracle.c');shutil.copyfile(fixture,folder/'runner.c')
 layout=elf_static_images(objects) if symbol=='image_statics' else None
 for index,obj in enumerate(objects):run(name+f'-readelf-{index}',['readelf','-aW',obj],folder)
 run(name+'-link',['cc','-std=c11','-Wall','-Wextra','-Werror',folder/'runner.c',*objects,'-Wl,-z,noexecstack','-o',folder/'runner'],folder)
 log=run(name+'-execute',[folder/'runner'],folder);assert 'PASS' in log
 record['cases'].append(dict(name=name,objects=[dict(name=obj.name,sha256=hashlib.sha256(obj.read_bytes()).hexdigest()) for obj in objects],elf=layout));save()
assert len(record['cases'])==2
record.update(complete=True,passed=True);save();print(json.dumps(record['cases']),flush=True)
