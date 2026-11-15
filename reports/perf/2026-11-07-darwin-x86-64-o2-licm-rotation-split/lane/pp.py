"""Pretty-print a dumped part: split the top-level assertion's conjunction into
definitions (= name term) and the negated claim, one per line, with depth-limited indentation."""
import sys, re
def tok(s):
    return re.findall(r'\(|\)|\|[^|]*\||[^\s()]+', s)
def parse(ts, i=0):
    if ts[i] == '(':
        out=[]; i+=1
        while ts[i] != ')':
            x,i = parse(ts,i); out.append(x)
        return out, i+1
    return ts[i], i+1
def show(e):
    if isinstance(e,str): return e
    return '(' + ' '.join(show(x) for x in e) + ')'
def flat_and(e, acc):
    if isinstance(e,list) and e and e[0]=='and':
        for x in e[1:]: flat_and(x, acc)
    else: acc.append(e)
src=open(sys.argv[1]).read()
ts=tok(src); i=0; cmds=[]
while i < len(ts):
    c,i=parse(ts,i); cmds.append(c)
for c in cmds:
    if c[0]=='assert':
        acc=[]; flat_and(c[1], acc)
        for a in acc:
            if isinstance(a,list) and a[0]=='not':
                print('CLAIM (negated):')
                inner=a[1]
                # (= true (and ...))
                if isinstance(inner,list) and inner[0]=='=' and inner[1]=='true':
                    cl=[]; flat_and(inner[2], cl)
                    for k,x in enumerate(cl): print(f'  [{k}] {show(x)}')
                else: print('  ', show(inner))
            else:
                print('DEF', show(a))
    elif c[0]=='declare-const':
        pass
print('DECLS', ' '.join(f"{c[1]}:{show(c[2])}" for c in cmds if c[0]=='declare-const'))
