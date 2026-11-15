from pathlib import Path
import json,re
p=Path('$HOME/trust-cg/target/fat-fn-spread-investigation')
for label in ['first','merged']:
 f=p/f'native-{label}-results.json'
 if not f.exists():continue
 rows=json.loads(f.read_text())
 if len(rows)!=3:continue
 assert all(r['returncode']==0 for r in rows)
 sums=dict(executions=0,checks=0,panics=0,aborts=0,refusals=0)
 receipts=[]
 for row in rows:
  s=Path(row['log']).read_text()
  for line in s.splitlines():
   if 'TCG_' not in line or 'backend_sha256=' not in line:continue
   receipts.append(line)
   for k in sums:
    m=re.search(r'\b'+k+r'=(\d+)',line)
    if m:sums[k]+=int(m.group(1))
 assert sums==dict(executions=66,checks=153668,panics=16384,aborts=16,refusals=6),sums
 (p/f'native-{label}-summary.json').write_text(json.dumps(dict(totals=sums,receipts=receipts),indent=2)+'\n');print(label,sums)
 f=p/f'proof-{label}-results.json'
 if not f.exists():continue
 sums=[]
 for row in json.loads(f.read_text()):
  mode,opt=row['mode'],row['opt'];s=(p/f'proof-{label}-{mode}-O{opt}/compile.log').read_text();traces=re.findall(r': (\d+) refined, (\d+) skipped .*?, (\d+) memo-hit',s);vals=[sum(int(t[i]) for t in traces) for i in range(3)];unmodeled=sum(map(int,re.findall(r'; (\d+) unmodeled shape',s)))
  assert row['returncode']==(0 if mode=='strict' else 1)
  if mode=='machine':assert 'TCG-PROOF-465' in s
  assert (len(traces),*vals,unmodeled)==(13,4,0,0,0)
  sums.append(dict(mode=mode,opt=opt,functions=len(traces),refined=vals[0],skipped=vals[1],memo_hits=vals[2],unmodeled=unmodeled))
 (p/f'proof-{label}-summary.json').write_text(json.dumps(sums,indent=2)+'\n')
