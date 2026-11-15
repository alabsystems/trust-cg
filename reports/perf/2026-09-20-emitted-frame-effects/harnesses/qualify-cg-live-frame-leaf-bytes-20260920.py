from pathlib import Path
import dataclasses,json,os,re,struct,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');out=r/'cg-live-frame-bounds-native-first';record=json.loads((out/'results.json').read_text());assert record['passed']
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
record['masked_leaf_checks']=[]
for level in [2,3]:
 name=f'bounds_unwind-O{level}';objects=list((out/name).glob('*.o'));assert len(objects)==1;obj=objects[0];raw=obj.read_bytes();assert raw[:6]==b'\x7fELF\x02\x01';off=struct.unpack_from('<Q',raw,40)[0];stride,count=struct.unpack_from('<HH',raw,58);sections=[struct.unpack_from('<IIQQQQIIQQ',raw,off+i*stride) for i in range(count)];functions=[]
 for section in sections:
  if section[1]!=2:continue
  strings=sections[section[6]];names=raw[strings[4]:strings[4]+strings[5]]
  for i in range(section[5]//section[9]):
   n,info,other,shndx,value,size=struct.unpack_from('<IBBHQQ',raw,section[4]+i*section[9])
   if info&15!=2 or not shndx:continue
   symbol=names[n:names.find(b'\0',n)].decode();slot=sections[shndx];code=raw[slot[4]+value:slot[4]+value+size]
   functions.append(dict(symbol=symbol,offset=value,size=size,hex=code.hex()))
 assert len(functions)==1 and functions[0]['symbol']=='bounds_unwind'
 assert bytes.fromhex(functions[0]['hex'])==struct.pack('<III',0x92400823,0xf8237802,0xd65f03c0),functions
 cmd=['readelf','--debug-dump=frames',str(obj)];result=guard.run_captured(cmd,16384,60,label=name+'-cfi',env={'PATH':'/usr/bin:/bin'},cwd=out)
 (out/(name+'-cfi.log')).write_text(result.stdout+result.stderr);assert not any([result.returncode,result.memout,result.timed_out,result.cancelled,result.stdout_truncated,result.stderr_truncated])
 cfi=result.stdout;assert 'Return address column: 30' in cfi and 'DW_CFA_def_cfa: r31 (sp) ofs 0' in cfi
 assert all(line.strip() in ['DW_CFA_def_cfa: r31 (sp) ofs 0','DW_CFA_nop'] for line in cfi.splitlines() if 'DW_CFA_' in line)
 ranges=[(int(a,16),int(b,16)) for a,b in re.findall(r'FDE .*pc=([0-9a-f]+)\.\.([0-9a-f]+)',cfi)];assert ranges==[(functions[0]['offset'],functions[0]['offset']+12)],ranges
 record['commands'].append(dict(name=name+'-cfi',command=cmd,**dataclasses.asdict(result)));record['masked_leaf_checks'].append(dict(name=name,functions=functions,exact_cfi_extent=True,cfa_sp_offset=0))
(out/'results.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record['masked_leaf_checks']),flush=True)
