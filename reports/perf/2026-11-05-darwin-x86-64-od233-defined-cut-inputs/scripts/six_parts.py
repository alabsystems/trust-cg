import re,sys
BODY='Source-bound x86-64 whole-body theorem (System V, pre-RA ISel): the replayed body theorem credits every covered value row'
fns=['cgu.0.1243._RNvMs0_NtNtCs7e1ihmkzmZ8_4core3fmt3numo10__fmt_inner','cgu.0.1958._RNvMsf','cgu.0.1975._RNvMsk','cgu.0.2044._RNvNtNtCs7e1ihmkzmZ8_4core10intrinsics8fallback13wide_mul_u128B5_','cgu.0.2117._RNvNtNtNtCs7e1ihmkzmZ8_4core3fmt3num3imp7exp_u64','cgu.0.2271._RNvNvNtNtCs7e1ihmkzmZ8_4core10intrinsics8fallback13wide_mul_u12810scalar_mul']
pend=[]; att={}
for line in open(sys.argv[1],errors='replace'):
    line=line.rstrip('\n')
    m=re.match(r'\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)',line)
    if m:
        for f in fns:
            if f in m.group(1) and pend:
                k=att.get(f,0); att[f]=k+1
                print(f'== {f[-45:]} attempt {k}')
                for p in pend: print('   ',p)
        pend=[]
    elif line.startswith('TCG_SOLVE_TRACE') and BODY in line:
        l=line.replace(BODY,'BODY')
        if 'claim' in l and 'Verified' in l: continue
        if 'promotion_result' in l and 'result=Verified' in l: continue
        pend.append(l[16:200])
    elif line.startswith('[TCG-X86-BODY-TRACE] replay'):
        pend.append(line[21:110])
