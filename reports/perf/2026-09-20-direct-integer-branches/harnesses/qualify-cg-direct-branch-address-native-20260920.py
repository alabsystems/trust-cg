from pathlib import Path
import dataclasses,hashlib,json,os,re,shutil,struct,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917');production=r/('cg-direct-branch-production-'+sys.argv[1]);out=r/('cg-direct-branch-address-native-'+sys.argv[1]);out.mkdir()
a=json.loads((production/'results.json').read_text());assert a['passed'] and a['complete']
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Direct address leaf native values and ABI')
record=dict(production_backend=a['backend'],source=a['source'],resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,commands=[],cases=[])
env=dict(os.environ);env['PATH']='/usr/bin:/bin'
def save():(out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
def run(label,cmd,cwd):
 result=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(out/(label+'.log')),*map(str,cmd)],16384,300,label=label,env=env,cwd=cwd)
 row=dataclasses.asdict(result);row.update(name=label,command=list(map(str,cmd)));record['commands'].append(row);save()
 assert result.returncode==0 and not any([result.timed_out,result.memout,result.cancelled,result.stdout_truncated,result.stderr_truncated]),label
 return (out/(label+'.log')).read_text()
def functions(path):
 raw=path.read_bytes();assert raw[:6]==b'\x7fELF\x02\x01'
 assert struct.unpack_from('<H',raw,18)[0]==183
 off=struct.unpack_from('<Q',raw,40)[0];stride,count=struct.unpack_from('<HH',raw,58)
 sections=[struct.unpack_from('<IIQQQQIIQQ',raw,off+i*stride) for i in range(count)]
 rows=[]
 for section in sections:
  if section[1]!=2:continue
  strings=sections[section[6]];names=raw[strings[4]:strings[4]+strings[5]]
  for i in range(section[5]//section[9]):
   n,info,other,shndx,value,size=struct.unpack_from('<IBBHQQ',raw,section[4]+i*section[9])
   name=names[n:names.find(b'\0',n)].decode()
   if info&15!=2 or not shndx:continue
   slot=sections[shndx];code=raw[slot[4]+value:slot[4]+value+size];assert len(code)==size and size%4==0
   words=[x[0] for x in struct.iter_unpack('<I',code)]
   assert words and words[-1]==0xd65f03c0,(name,words)
   for word in words[:-1]:
    if word&0x9f000000==0x90000000:assert word&31<16
    elif word&0xffc00000==0x91000000:assert word&31<16 and (word>>5)&31<16
    elif word&0xffe0ffe0==0xaa0003e0:assert word&31<16 and (word>>16)&31<16
    else:assert word==0xd503201f,(name,hex(word))
   rows.append(dict(name=name,offset=value,bytes=size,instructions=[hex(w) for w in words]))
 return rows
for case in a['cases']:
 if not case['name'].startswith('image_'):continue
 name=case['name'];symbol=name.rsplit('-O',1)[0]
 if symbol=='bounds_unwind':
  assert not case['production_admitted'] and case['proof_refusal'];continue
 assert case['production_admitted'],case
 folder=out/name;folder.mkdir();objects=[]
 for original in sorted((production/name).glob('*.o')):
  obj=folder/original.name;shutil.copyfile(original,obj);objects.append(obj)
 assert objects
 source={'image_aligned':r/'cg-const-references-aligned-oracle.c','image_scalars':r/'cg-global-address-leaf-scalars-oracle.c','image_statics':r/'cg-const-references-static-oracle.c'}[symbol]
 driver=source.read_text();inspections=[];abi=[]
 if symbol!='image_statics':
  for obj in objects:inspections.extend(functions(obj))
  expected=['image_aligned','image_literal'] if symbol=='image_aligned' else ['image_i64','image_u128','image_bool','image_char','image_f32','image_f64','image_array']
  assert sorted(row['name'] for row in inspections)==sorted(expected),inspections
  template=(r/'cg-frameless-output-native-first/abi.S').read_text()
  for fn in expected:
   driver=driver.replace(fn+'(', 'checked_'+fn+'(')
   wrapper=folder/(fn+'.S');wrapper.write_text(template.replace('output_memory_writer',fn));abi.append(wrapper)
 (folder/'runner.c').write_text(driver)
 for index,obj in enumerate(objects):
  run(name+f'-readelf-{index}',['readelf','-aW',obj],folder)
  run(name+f'-disassemble-{index}',['objdump','-dr',obj],folder)
  cfi=run(name+f'-cfi-{index}',['readelf','--debug-dump=frames',obj],folder)
  if symbol!='image_statics':
   assert 'Return address column: 30' in cfi and 'DW_CFA_def_cfa: r31 (sp) ofs 0' in cfi
   assert all(line.strip() in ['DW_CFA_def_cfa: r31 (sp) ofs 0','DW_CFA_nop'] for line in cfi.splitlines() if 'DW_CFA_' in line),cfi
   ranges=[(int(start,16),int(end,16)) for start,end in re.findall(r'FDE .*pc=([0-9a-f]+)\.\.([0-9a-f]+)',cfi)]
   assert sorted(ranges)==sorted((f['offset'],f['offset']+f['bytes']) for f in functions(obj)),(ranges,functions(obj))
 run(name+'-link',['cc','-std=c11','-Wall','-Wextra','-Werror',folder/'runner.c',*objects,*abi,'-Wl,-z,noexecstack','-o',folder/'runner'],folder)
 log=run(name+'-execute',[folder/'runner'],folder);assert 'PASS' in log
 record['cases'].append(dict(name=name,objects=[dict(name=obj.name,sha256=hashlib.sha256(obj.read_bytes()).hexdigest()) for obj in objects],leaf_function_instructions=inspections,abi_checked=bool(abi),cfi_checked=bool(abi)));save()
assert len(record['cases'])==6
record.update(complete=True,passed=True);save();print(json.dumps(record['cases']),flush=True)
