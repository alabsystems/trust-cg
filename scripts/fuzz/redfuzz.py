#!/usr/bin/env python3
"""
Soundness fuzzer for the reduction-split pass. Generates constant-trip integer
reduction loops (what the pass FIRES on) + must-bail cases, compiles each with
trust-cg -O0/-O2/-O3 and clang -O2, asserts ALL results IDENTICAL (a miscompiling
split => O0 != O2), and checks O2 == O3 (idempotence).
usage: redfuzz.py <trust-cg-binary>
"""
import sys, os, subprocess, tempfile, shutil, itertools

OPS = {'add': ('add', '+', 0), 'mul': ('mul', '*', 1),
       'or': ('or', '|', 0), 'xor': ('xor', '^', 0)}
WIDTHS = {'i64': ('uint64_t', 'unsigned long long', '%llu'),
          'i32': ('uint32_t', 'unsigned', '%u')}

def gen_tir(op, w, term, limit, start):
    mnem, _cop, init = OPS[op]
    n = [0]
    def nid():
        n[0] += 1
        return n[0]
    limit_id, start_id, one_id, init_id, c3, c7 = (nid() for _ in range(6))
    consts = [
        f"    %{limit_id} = const {w} {limit}",
        f"    %{start_id} = const {w} {start}",
        f"    %{one_id} = const {w} 1",
        f"    %{init_id} = const {w} {init}",
        f"    %{c3} = const {w} 3",
        f"    %{c7} = const {w} 7",
    ]
    i_p, acc_p = nid(), nid()
    cmp_id = nid()
    i2, acc2 = nid(), nid()
    tinsts = []
    if term == 'i':
        t = i2
    elif term == 'ii':
        r = nid(); tinsts.append(f"    %{r} = mul {w} %{i2}, %{i2}"); t = r
    elif term == 'mix':
        a, b, c = nid(), nid(), nid()
        tinsts += [f"    %{a} = mul {w} %{i2}, %{i2}",
                   f"    %{b} = mul {w} %{i2}, %{c3}",
                   f"    %{c} = xor {w} %{a}, %{b}"]
        t = c
    elif term == 'i7':
        r = nid(); tinsts.append(f"    %{r} = mul {w} %{i2}, %{c7}"); t = r
    elif term == 'ior1':
        r = nid(); tinsts.append(f"    %{r} = or {w} %{i2}, %{one_id}"); t = r
    accN, iN, rp = nid(), nid(), nid()
    tinsts.append(f"    %{accN} = {mnem} {w} %{acc2}, %{t}")
    tinsts.append(f"    %{iN} = add {w} %{i2}, %{one_id}")
    nl = chr(10)
    return f"""; TrustIr text format v1
module "r"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = () -> ({w})
fn @kernel(functy.0) {{
bb0():
{nl.join(consts)}
    br bb1(%{start_id}, %{init_id})
bb1(%{i_p}: {w}, %{acc_p}: {w}):
    %{cmp_id} = icmp sge {w} %{i_p}, %{limit_id}
    condbr %{cmp_id}, bb2(%{acc_p}), bb3(%{i_p}, %{acc_p})
bb3(%{i2}: {w}, %{acc2}: {w}):
{nl.join(tinsts)}
    br bb1(%{iN}, %{accN})
bb2(%{rp}: {w}):
    ret %{rp}
}}
"""

def gen_c(op, w, term, limit, start):
    cty, _, fmt = WIDTHS[w]
    _, cop, init = OPS[op]
    texpr = {'i': 'i', 'ii': 'i*i', 'mix': '(i*i)^(i*3)', 'i7': 'i*7', 'ior1': '(i|1)'}[term]
    return f"""#include <stdint.h>
{cty} kernel(void){{ {cty} a={init}; for({cty} i={start};i<{limit};i++){{ a = a {cop} ({cty})({texpr}); }} return a; }}
"""

# must-bail adversarial trust_ir kernels (must be left correct: O0==O2==O3)
BAIL = {
    # acc used in the term -> splitting would miscompile
    'accbody': """; TrustIr text format v1
module "b"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = () -> (i64)
fn @kernel(functy.0) {
bb0():
    %1 = const i64 40000
    %2 = const i64 0
    %3 = const i64 1
    %4 = const i64 7
    br bb1(%2, %2)
bb1(%5: i64, %6: i64):
    %7 = icmp sge i64 %5, %1
    condbr %7, bb2(%6), bb3(%5, %6)
bb3(%8: i64, %9: i64):
    %10 = and i64 %9, %4
    %11 = add i64 %10, %8
    %12 = add i64 %9, %11
    %13 = add i64 %8, %3
    br bb1(%13, %12)
bb2(%14: i64):
    ret %14
}
""",
    # subtraction reduction -> non-associative, must not split
    'subred': """; TrustIr text format v1
module "b"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = () -> (i64)
fn @kernel(functy.0) {
bb0():
    %1 = const i64 40000
    %2 = const i64 0
    %3 = const i64 1
    br bb1(%2, %2)
bb1(%5: i64, %6: i64):
    %7 = icmp sge i64 %5, %1
    condbr %7, bb2(%6), bb3(%5, %6)
bb3(%8: i64, %9: i64):
    %10 = mul i64 %8, %8
    %11 = sub i64 %9, %10
    %13 = add i64 %8, %3
    br bb1(%13, %11)
bb2(%14: i64):
    ret %14
}
""",
}
BAIL_C = {
    'accbody': "#include <stdint.h>\nuint64_t kernel(void){uint64_t a=0;for(uint64_t i=0;i<40000;i++)a+=(a&7)+i;return a;}\n",
    'subred':  "#include <stdint.h>\nuint64_t kernel(void){uint64_t a=0;for(uint64_t i=0;i<40000;i++)a-=i*i;return a;}\n",
}

DRIVER = {
    'i64': '#include <stdio.h>\n#include <stdint.h>\nextern uint64_t kernel(void);\nint main(){printf("%llu\\n",(unsigned long long)kernel());return 0;}\n',
    'i32': '#include <stdio.h>\n#include <stdint.h>\nextern uint32_t kernel(void);\nint main(){printf("%u\\n",(unsigned)kernel());return 0;}\n',
}

def run_one(tcg, tir_text, c_text, w, wd, idx):
    tir = os.path.join(wd, f"k{idx}.trust_ir"); open(tir,"w").write(tir_text)
    drv = os.path.join(wd, f"d{idx}.c"); open(drv,"w").write(DRIVER[w])
    res = {}
    for o in ("O0","O2","O3"):
        obj = os.path.join(wd, f"k{idx}_{o}.o")
        r = subprocess.run([tcg,"--format=text","--target","aarch64",f"-{o}","-c",tir,"-o",obj],
                           capture_output=True, text=True)
        if r.returncode != 0:
            return ("COMPILE_ERR", o, (r.stderr or r.stdout).strip().splitlines()[-1][:150] if (r.stderr or r.stdout).strip() else "")
        b = os.path.join(wd, f"k{idx}_{o}.bin")
        if subprocess.run(["cc",drv,obj,"-o",b],capture_output=True).returncode!=0:
            return ("LINK_ERR", o, "")
        res[o] = subprocess.run([b],capture_output=True,text=True).stdout.strip()
    # clang reference
    cf = os.path.join(wd, f"k{idx}.c"); open(cf,"w").write(c_text)
    cobj = os.path.join(wd, f"k{idx}_clang.o")
    subprocess.run(["cc","-O2","-c",cf,"-o",cobj],capture_output=True)
    cb = os.path.join(wd, f"k{idx}_clang.bin")
    subprocess.run(["cc",DRIVER_FILE(wd,w),cobj,"-o",cb],capture_output=True)
    res['clang'] = subprocess.run([cb],capture_output=True,text=True).stdout.strip()
    vals = set(res.values())
    if len(vals) != 1:
        return ("MISMATCH", "", res)
    return ("OK", "", res['O0'])

def DRIVER_FILE(wd,w):
    p=os.path.join(wd,f"drv_{w}.c")
    if not os.path.exists(p): open(p,"w").write(DRIVER[w])
    return p

def main():
    tcg = sys.argv[1]
    wd = tempfile.mkdtemp(prefix="redfuzz_")
    ok=miscompile=other=0; mism=[]; errs=[]
    idx=0
    limits=[0,1,7,8,100,40001]  # mix of ÷4 (fires) and not (bails)
    starts=[0,1,5]
    for op in OPS:
        for w in WIDTHS:
            for term in ['i','ii','mix','i7','ior1']:
                for limit in limits:
                    for start in starts:
                        if start>=limit and limit!=0: continue
                        idx+=1
                        cat,o,info = run_one(tcg, gen_tir(op,w,term,limit,start),
                                             gen_c(op,w,term,limit,start), w, wd, idx)
                        if cat=="OK": ok+=1
                        elif cat=="MISMATCH": miscompile+=1; mism.append((f"{op}/{w}/{term} [{start},{limit})", info))
                        else: other+=1; errs.append((f"{op}/{w}/{term} [{start},{limit})", cat, o, info))
    # must-bail cases
    for name in BAIL:
        idx+=1
        cat,o,info = run_one(tcg, BAIL[name], BAIL_C[name], 'i64', wd, idx)
        if cat=="OK": ok+=1
        elif cat=="MISMATCH": miscompile+=1; mism.append((f"BAIL:{name}", info))
        else: other+=1; errs.append((f"BAIL:{name}", cat, o, info))
    print(f"\n=== reduction-split soundness: {idx} kernels ===")
    print(f"OK(O0==O2==O3==clang)={ok}  MISMATCH={miscompile}  other(compile/link)={other}")
    if mism:
        print("\n!!! MISMATCHES (pass changed the result — MISCOMPILE):")
        for d,info in mism: print(f"   {d}: {info}")
    if errs:
        print(f"\n?? non-OK/non-mismatch ({len(errs)}):")
        for d,cat,o,info in errs[:15]: print(f"   {d}: {cat} {o} {info}")
    shutil.rmtree(wd, ignore_errors=True)
    sys.exit(1 if miscompile else 0)

if __name__=="__main__":
    main()
