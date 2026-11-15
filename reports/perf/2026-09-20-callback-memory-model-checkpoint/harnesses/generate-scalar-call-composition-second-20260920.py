"""Conditional single-call framing prototype; no compiler admission authority.

External effects depend only on projected public memory and arguments. Private
save preservation is modeled explicitly. A typed C declaration alone supplies
neither premise. Every output query is a complete negated conjunction.
"""
from pathlib import Path
import hashlib,json
out=Path('/home/ayates/trust-cg-soundness-20260914/scalar-call-composition-prototype-second')
out.mkdir(exist_ok=True)
assert not any(out.iterdir())
ARR='(Array (_ BitVec 64) (_ BitVec 8))'
def bv(n,w=64):return f'(_ bv{n} {w})'
def call(name,*args):return '('+' '.join([name,*args])+')'
def add(a,n):return call('bvadd',a,bv(n))
def below(n):return call('bvsub','entry_sp',bv(n))
def store_le(mem,addr,value,width):
    for i in range(width):
        byte=f'((_ extract {8*i+7} {8*i}) {value})'
        mem=call('store',mem,add(addr,i),byte)
    return mem

def load_le(mem,addr,width):
    vals=[call('select',mem,add(addr,i)) for i in reversed(range(width))]
    result=vals[0]
    for byte in vals[1:]:result=call('concat',result,byte)
    return result

def make(width,mutant):
    lines=['; Diagnostic conditional ABI call framing. Not source or byte proof.',
           '(set-logic QF_AUFBV)','(set-option :produce-models true)']
    def decl(name,sort):lines.append(f'(declare-fun {name} () {sort})')
    def define(name,sort,expr):lines.append(f'(define-fun {name} () {sort} {expr})');return name
    for name in ['entry_sp','entry_x20','entry_x19','entry_fp','entry_lr','observe']:
        decl(name,'(_ BitVec 64)')
    for name in ['cell_before','argument']:decl(name,f'(_ BitVec {8*width})')
    decl('entry_memory',ARR)
    lines.append(f'(declare-fun callback ({ARR} (_ BitVec 64) (_ BitVec {8*width})) {ARR})')
    if mutant=='wrong_target':lines.append(f'(declare-fun wrong_callback ({ARR} (_ BitVec 64) (_ BitVec {8*width})) {ARR})')
    cell=define('cell','(_ BitVec 64)',below(32+width))
    private=[('entry_x20',32),('entry_x19',24),('entry_fp',16),('entry_lr',8)]
    m='entry_memory'
    for name,n in private:
        address=below(32 if mutant=='wrong_save_offset' and name=='entry_x19' else n)
        m=define('saved_'+name,ARR,store_le(m,address,name,8))
    source=define('source_before',ARR,store_le('entry_memory',cell,'cell_before',width))
    machine_width=(8 if width==4 else 4) if mutant=='wrong_cell_width' else width
    machine_value='cell_before'
    if machine_width>width:machine_value='((_ zero_extend 32) cell_before)'
    if machine_width<width:machine_value='((_ extract 31 0) cell_before)'
    machine=define('machine_before',ARR,store_le(m,cell,machine_value,machine_width))
    def project(mem):
        for i in range(32):mem=call('store',mem,add(below(32),i),bv(0,8))
        return mem
    source_input=define('source_public_input',ARR,project(source))
    machine_input=define('machine_public_input',ARR,project(machine))
    source_post=define('source_call_result',ARR,call('callback',source_input,cell,'argument'))
    target='wrong_callback' if mutant=='wrong_target' else 'callback'
    pointer=add(cell,1) if mutant=='wrong_pointer' else cell
    argument=call('bvxor','argument',bv(1,8*width)) if mutant=='wrong_argument' else 'argument'
    visible=machine if mutant=='private_read' else machine_input
    machine_post=define('machine_call_result',ARR,call(target,visible,pointer,argument))
    if mutant=='drop_public_effects':
        machine_post=define('lost_public_effects',ARR,store_le(source,cell,load_le(machine_post,cell,width),width))
    if mutant=='stale_cell':
        machine_post=define('stale_cell',ARR,store_le(machine_post,cell,'cell_before',width))
    restored=machine_post
    for i in range(32):
        if mutant=='private_write' and i==8:continue
        addr=add(below(32),i)
        restored=call('store',restored,addr,call('select',machine,addr))
    restored=define('machine_after_call',ARR,restored)
    sp=call('bvadd',call('bvadd',call('bvsub',call('bvsub','entry_sp',bv(32)),bv(16)),bv(16)),bv(16 if mutant=='wrong_sp' else 32))
    properties=[call('=',sp,'entry_sp'),call('=',source_input,machine_input)]
    for name,n in private:properties.append(call('=',load_le(restored,below(n),8),name))
    properties.append(call('=',load_le(restored,cell,width),load_le(source_post,cell,width)))
    outside=call('or',call('bvult','observe',below(48)),call('bvuge','observe','entry_sp'))
    properties.append(call('=>',outside,call('=',call('select',restored,'observe'),call('select',source_post,'observe'))))
    lines.extend([call('assert',call('bvuge','entry_sp',bv(48))),
                  call('assert',call('=',call('bvand','entry_sp',bv(15)),bv(0))),
                  call('assert',call('not',call('and',*properties))),
                  '(check-sat)','(exit)'])
    return ('\n'.join(lines)+'\n').encode()
rows=[]
for width in [4,8]:
    for variant in ['framed','private_read','private_write','wrong_target','wrong_pointer','wrong_argument','drop_public_effects','stale_cell','wrong_sp','wrong_save_offset','wrong_cell_width']:
        raw=make(width,variant);name=f'cell{8*width}-{variant}.smt2';(out/name).write_bytes(raw)
        rows.append(dict(query=name,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),expected='unsat' if variant=='framed' else 'sat'))
(out/'manifest.json').write_text(json.dumps(dict(scope=__doc__,tested=False,source_generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),queries=rows),indent=2)+'\n')
print(json.dumps(dict(generated=len(rows),tested=False,directory=str(out))))
