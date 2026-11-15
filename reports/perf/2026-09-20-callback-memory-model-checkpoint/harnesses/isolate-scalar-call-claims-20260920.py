from pathlib import Path
import hashlib,json,re
r=Path('/home/ayates/trust-cg-soundness-20260914')
source=r/'scalar-call-composition-prototype-normalized';out=r/'scalar-call-composition-claims';out.mkdir()
rows=[]
def parse(s):
    tokens=re.findall(r'\(|\)|[^\s()]+',s)
    def one(i):
        if tokens[i]!='(':return tokens[i],i+1
        values=[];i+=1
        while tokens[i]!=')':
            value,i=one(i);values.append(value)
        return values,i+1
    value,i=one(0);assert i==len(tokens);return value

def render(x):return '('+' '.join(map(render,x))+')' if isinstance(x,list) else x
names=['sp','public_input','x20','x19','fp','lr','cell_result','public_result']
for width in [32,64]:
    parent=source/f'cell{width}-framed.smt2';raw=parent.read_text();lines=raw.splitlines()
    at=[i for i,line in enumerate(lines) if line.startswith('(assert (not (and ')];assert len(at)==1
    expr=parse(lines[at[0]]);assert expr[0]=='assert' and expr[1][0]=='not' and expr[1][1][0]=='and'
    conjuncts=expr[1][1][1:];assert len(conjuncts)==len(names)
    for label,claim in zip(names,conjuncts):
        modified=lines.copy();modified[at[0]]=render(['assert',['not',claim]])
        data=('\n'.join(modified)+'\n').encode();name=f'cell{width}-{label}.smt2';(out/name).write_bytes(data)
        rows.append(dict(query=name,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),expected='unsat',parent_sha256=hashlib.sha256(parent.read_bytes()).hexdigest(),claim=label))
    (out/f'cell{width}-private_write.smt2').write_bytes((source/f'cell{width}-private_write.smt2').read_bytes())
(out/'manifest.json').write_text(json.dumps(dict(scope='Diagnostic conjunct isolation, NOT a complete whole-call theorem or compiler admission. Original source query and exact selected conjunct are retained.',queries=rows),indent=2)+'\n')
print('Generated 16 diagnostic conjuncts with original guards and definitions.')
s=(r/'probe-scalar-call-composition-normalized-20260920.py').read_text().replace("source=r/'scalar-call-composition-prototype-normalized'", "source=r/'scalar-call-composition-claims'")
s=s.replace("name.replace('-framed','-private_write')", "name.split('-')[0]+'-private_write'")
s=s.replace("scope='Standalone conditional single-call memory model.", "scope='Diagnostic per-conjunct isolation, not complete call composition. Standalone conditional single-call memory model.")
(r/'probe-scalar-call-claims-20260920.py').write_text(s)
