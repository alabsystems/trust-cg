from pathlib import Path
import dataclasses,hashlib,json,os,shutil,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');production=r/'cg-zero-storage-bounds-production-first';out=r/'cg-zero-storage-bounds-production-native-first';out.mkdir()
a=json.loads((production/'results.json').read_text());assert a['passed'] and a['complete']
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Canonical bounds normal backend native endpoints')
record=dict(production_backend=a['backend'],source=a['source'],resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,commands=[],cases=[])
env=dict(os.environ);env['PATH']='/usr/bin:/bin'
def save():(out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
def run(label,cmd,cwd):
 result=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(out/(label+'.log')),*map(str,cmd)],16384,300,label=label,env=env,cwd=cwd)
 row=dataclasses.asdict(result);row.update(name=label,command=list(map(str,cmd)));record['commands'].append(row);save()
 assert result.returncode==0 and not any([result.timed_out,result.memout,result.cancelled,result.stdout_truncated,result.stderr_truncated]),label
 return (out/(label+'.log')).read_text()
old=r/'cg-frameless-output-native-first'
for case in a['cases']:
 if not case['production_admitted']:continue
 name=case['name'];symbol=name.rsplit('-O',1)[0];folder=out/name;folder.mkdir()
 objects=list((production/name).glob('*.o'));assert len(objects)==1
 obj=folder/objects[0].name;shutil.copyfile(objects[0],obj)
 if symbol=='output_memory_writer':
  for filename in ['runner.c','abi.S']:shutil.copyfile(old/filename,folder/filename)
 else:
  modes={'bounds_const':0,'bounds_mask':1,'bounds_dominated':2,'bounds_dynamic':3,'bounds_unwind':1};mode=modes[symbol]
  (folder/'abi.S').write_text((old/'abi.S').read_text().replace('output_memory_writer',symbol))
  (folder/'runner.c').write_text('''#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>
extern void checked_FUNCTION(uint64_t *, uint64_t, uint64_t);
int main(void) {
  struct rlimit limit={0,0}; if(setrlimit(RLIMIT_CORE,&limit))return 10;
  uint64_t *arena=mmap(0,4096,PROT_READ|PROT_WRITE,MAP_SHARED|MAP_ANONYMOUS,-1,0);
  if(arena==MAP_FAILED)return 11;
  const uint64_t indices[]={0,1,7,8,UINT64_MAX,UINT64_C(1)<<32,UINT64_C(1)<<63};
  uint64_t seed=0x123456789abcdefULL,before[16];
  for(unsigned row=0;row<257;row++) {
    uint64_t index=indices[row%7];if(MODE==3)index=row%8;
    unsigned start=1+row%8;
    for(unsigned i=0;i<16;i++)arena[i]=before[i]=0xa5a5a5a5a5a5a5a5ULL^(row*16+i);
    seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;
    uint64_t value=row==0?0:row==1?UINT64_MAX:seed;
    checked_FUNCTION(arena+start,index,value);
    uint64_t offset=MODE==0?3:MODE==1?(index&7):index;
    for(unsigned i=0;i<16;i++) {
      uint64_t expected=(offset<8 && i==start+offset)?value:before[i];
      if(arena[i]!=expected)return 12;
    }
  }
  if(MODE==3)for(unsigned bad=3;bad<7;bad++) {
    for(unsigned i=0;i<16;i++)arena[i]=before[i]=0xbeeffeedcafef00dULL+i;
    pid_t child=fork();if(child<0)return 13;
    if(child==0){checked_FUNCTION(arena+1,indices[bad],42);_exit(99);}
    int status=0;if(waitpid(child,&status,0)!=child)return 14;
    if(!WIFSIGNALED(status)||WTERMSIG(status)!=SIGTRAP)return 15;
    for(unsigned i=0;i<16;i++)if(arena[i]!=before[i])return 16;
  }
  puts("native checks PASS");return 0;
}
'''.replace('FUNCTION',symbol).replace('MODE',str(mode)))
 run(name+'-disassemble',['objdump','-dr',obj],folder)
 run(name+'-link',['cc','-std=c11','-Wall','-Wextra','-Werror',folder/'runner.c',obj,folder/'abi.S','-o',folder/'runner'],folder)
 log=run(name+'-execute',[folder/'runner'],folder);assert 'native checks PASS' in log
 record['cases'].append(dict(name=name,calls=257,arena_words=16,abi_checked=True,object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest()));save()
assert len(record['cases'])==sum(c['production_admitted'] for c in a['cases'])
assert any(c['name']=='output_memory_writer-O0' for c in record['cases']), 'O0 writer still not admitted'
record.update(complete=True,passed=True);save();print(json.dumps(record['cases']),flush=True)
