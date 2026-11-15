"""evalmodel.py <part.smt2> <ay-output-with-model>: evaluate the part's definitions and every
conjunct of its negated claim under AY's model; print which claim conjuncts are FALSE
(the observables the counterexample breaks) and the free inputs the model sets."""
import sys, re
sys.path.insert(0, '/dev/null')
def tok(s): return re.findall(r'\(|\)|\|[^|]*\||[^\s()]+', s)
def parse(ts, i=0):
    if ts[i] == '(':
        out=[]; i+=1
        while ts[i] != ')':
            x,i = parse(ts,i); out.append(x)
        return out, i+1
    return ts[i], i+1
def parse_all(s):
    ts=tok(s); i=0; out=[]
    while i < len(ts):
        c,i=parse(ts,i); out.append(c)
    return out
def width(sort):
    if sort=='Bool': return 0
    return int(sort[2])
def lit(s):
    if s.startswith('#x'): return int(s[2:],16), 4*(len(s)-2)
    if s.startswith('#b'): return int(s[2:],2), len(s)-2
    raise ValueError(s)
def ev(e, env, w):
    if isinstance(e,str):
        if e=='true': return True
        if e=='false': return False
        if e.startswith('#'): return lit(e)[0]
        return env[e]
    h=e[0]
    if isinstance(h,list):  # indexed op
        op=h[1]
        if op=='extract':
            hi,lo=int(h[2]),int(h[3]); return (ev(e[1],env,w)>>lo) & ((1<<(hi-lo+1))-1)
        if op=='zero_extend': return ev(e[1],env,w)
        if op=='sign_extend':
            n=int(h[2]); x=ev(e[1],env,w); iw=bw(e[1],w)
            return x | (((1<<n)-1)<<iw) if (x>>(iw-1))&1 else x
        raise ValueError(op)
    if h=='_' : return int(e[1][2:])
    a=[x for x in e[1:]]
    if h=='not': return not ev(a[0],env,w)
    if h=='and': return all(ev(x,env,w) for x in a)
    if h=='or': return any(ev(x,env,w) for x in a)
    if h=='=>': return (not ev(a[0],env,w)) or ev(a[1],env,w)
    if h=='=': return ev(a[0],env,w)==ev(a[1],env,w)
    if h=='ite': return ev(a[1],env,w) if ev(a[0],env,w) else ev(a[2],env,w)
    n=bw(a[0],w); m=(1<<n)-1
    x=ev(a[0],env,w); y=ev(a[1],env,w) if len(a)>1 else None
    s=lambda v: v-(1<<n) if (v>>(n-1))&1 else v
    if h=='bvult': return x<y
    if h=='bvule': return x<=y
    if h=='bvugt': return x>y
    if h=='bvuge': return x>=y
    if h=='bvslt': return s(x)<s(y)
    if h=='bvsle': return s(x)<=s(y)
    if h=='bvsgt': return s(x)>s(y)
    if h=='bvsge': return s(x)>=s(y)
    if h=='bvadd': 
        r=x
        for z in a[1:]: r=(r+ev(z,env,w))&m
        return r
    if h=='bvsub': return (x-y)&m
    if h=='bvmul': return (x*y)&m
    if h=='bvand':
        r=x
        for z in a[1:]: r&=ev(z,env,w)
        return r
    if h=='bvor':
        r=x
        for z in a[1:]: r|=ev(z,env,w)
        return r
    if h=='bvxor': return x^y
    if h=='bvnot': return (~x)&m
    if h=='bvneg': return (-x)&m
    if h=='bvshl': return (x<<y)&m if y<n else 0
    if h=='bvlshr': return x>>y if y<n else 0
    if h=='concat': return (x<<bw(a[1],w))|y
    raise ValueError(h)
def bw(e,w):
    if isinstance(e,str):
        if e.startswith('#'): return lit(e)[1]
        return w[e]
    h=e[0]
    if isinstance(h,list):
        if h[1]=='extract': return int(h[2])-int(h[3])+1
        if h[1] in ('zero_extend','sign_extend'): return int(h[2])+bw(e[1],w)
    if h=='_': return int(e[2])
    if h=='concat': return bw(e[1],w)+bw(e[2],w)
    if h=='ite': return bw(e[2],w)
    return bw(e[1],w)
def show(e): return e if isinstance(e,str) else '('+' '.join(show(x) for x in e)+')'
def flat_and(e, acc):
    if isinstance(e,list) and e and e[0]=='and':
        for x in e[1:]: flat_and(x, acc)
    else: acc.append(e)
q=parse_all(open(sys.argv[1]).read())
mtxt=open(sys.argv[2]).read()
mi=mtxt.index('(model'); mo=parse_all(mtxt[mi:mtxt.index('\n)',mi)+2])[0]
env={}; w={}
for c in q:
    if c[0]=='declare-const': w[c[1]]=width(c[2] if isinstance(c[2],str) else c[2])
for d in mo[1:]:
    env[d[1]]=lit(d[4])[0]
defs=set(); claims=[]
for c in q:
    if c[0]!='assert': continue
    acc=[]; flat_and(c[1],acc)
    for a in acc:
        if isinstance(a,list) and a[0]=='not':
            inner=a[1]; cl=[]; flat_and(inner[2] if inner[0]=='=' and inner[1]=='true' else inner, cl); claims=cl
        else:
            assert a[0]=='=' and isinstance(a[1],str); defs.add(a[1])
            v=ev(a[2],env,w); v=int(v) if isinstance(v,bool) else v
            assert env[a[1]]==v, (a[1], env[a[1]], v)
free=[n for n in w if n not in defs]
print('free inputs the model sets:', ', '.join(f'{n}={env[n]:#x}' for n in free))
for k,c in enumerate(claims):
    if not ev(c,env,w): print(f'FALSE claim [{k}]: {show(c)}')
