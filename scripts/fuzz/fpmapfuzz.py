#!/usr/bin/env python3
"""
Bit-identity differential fuzzer for the neon-fmap elementwise-FP vectorizer.

For each generated FP kernel (map / saxpy / stencil / in-place / count-above,
f32 AND f64) compiles three ways:
  - trust-cg -O2                                        (pass ON = vectorized)
  - trust-cg -O2 TRUST_CG_DISABLE_PASSES=neon_fmap      (pass OFF = scalar)
  - clang    -O2 -ffp-contract=off                      (reference)
and runs across many n (0,1,tails,16-multiples,large odd) over arrays SEEDED
WITH FP SPECIAL VALUES — quiet NaNs (two payloads), a signaling-NaN bit
pattern, +/-Inf, +/-0.0, denormals (min subnormal + random subnormals),
FLT/DBL_MAX/MIN and random finite values — requiring the ENTIRE OUTPUT
(array bytes, or the count value) to be BIT-IDENTICAL for on == off == clang.

Also an ALIASING NEGATIVE: the two-pointer map kernel compiled WITHOUT
noalias must NOT vectorize (no st1 in disasm) and must stay correct when
driven with fully-overlapping pointers.

usage: fpmapfuzz.py <trust-cg-binary> [--quick]
"""
import sys, os, subprocess, tempfile

TCG = sys.argv[1]
QUICK = "--quick" in sys.argv

HDR = '; TrustIr text format v1\nmodule "k"\ntarget "aarch64-apple-darwin" 8 little abi="aapcs64"\n'

# ---------------------------------------------------------------------------
# Kernel space: (name, family, needs_noalias, ir-builder, c-expr)
# Streams: 'b','c' = distinct input arrays; 'a' = the output array (in-place
# when read); s[i-1]/s[i+1] shifted reads of input 'b'.
# Invariants: K1=2.5, K2=1.0, K3=3.0 (fdiv divisor), P = scalar param.
# ---------------------------------------------------------------------------

def term_lines(kind, fty, ids):
    """Return (lines, result_id, loads_spec) where loads_spec is a list of
    (letter, offset) the kernel reads."""
    L = []
    n = [100]
    def nid():
        n[0] += 1
        return n[0]
    def load(letter, off):
        # index expr
        if off == 0:
            idx = ids['i']
        else:
            j = nid()
            op = 'add' if off > 0 else 'sub'
            L.append(f" %{j}={op} i32 %{ids['i']},%{ids['c' + str(abs(off))]}")
            idx = j
        g, v = nid(), nid()
        L.append(f" %{g}=gep {fty},ptr %{ids[letter]},%{idx}")
        L.append(f" %{v}=load {fty},ptr %{g}")
        return v
    if kind == 'map_mul_add':      # a[i] = b[i]*K1 + K2
        b = load('b', 0); m, r = nid(), nid()
        L.append(f" %{m}=fmul {fty} %{b},%{ids['K1']}")
        L.append(f" %{r}=fadd {fty} %{m},%{ids['K2']}")
        return L, r, [('b', 0)]
    if kind == 'map_sub':          # a[i] = b[i] - c[i]
        b = load('b', 0); c = load('c', 0); r = nid()
        L.append(f" %{r}=fsub {fty} %{b},%{c}")
        return L, r, [('b', 0), ('c', 0)]
    if kind == 'map_mul2':         # a[i] = b[i] * c[i]
        b = load('b', 0); c = load('c', 0); r = nid()
        L.append(f" %{r}=fmul {fty} %{b},%{c}")
        return L, r, [('b', 0), ('c', 0)]
    if kind == 'map_div':          # a[i] = b[i] / c[i]  (lane-wise FDIV)
        b = load('b', 0); c = load('c', 0); r = nid()
        L.append(f" %{r}=fdiv {fty} %{b},%{c}")
        return L, r, [('b', 0), ('c', 0)]
    if kind == 'map_divk':         # a[i] = b[i] / K3
        b = load('b', 0); r = nid()
        L.append(f" %{r}=fdiv {fty} %{b},%{ids['K3']}")
        return L, r, [('b', 0)]
    if kind == 'saxpy':            # a[i] = P*b[i] + a[i]
        b = load('b', 0); a = load('a', 0); m, r = nid(), nid()
        L.append(f" %{m}=fmul {fty} %{ids['P']},%{b}")
        L.append(f" %{r}=fadd {fty} %{m},%{a}")
        return L, r, [('b', 0), ('a', 0)]
    if kind == 'inplace':          # a[i] = a[i]*a[i] + K2 (single-array)
        a = load('a', 0); m, r = nid(), nid()
        L.append(f" %{m}=fmul {fty} %{a},%{a}")
        L.append(f" %{r}=fadd {fty} %{m},%{ids['K2']}")
        return L, r, [('a', 0)]
    if kind == 'stencil3':         # a[i] = (b[i-1]+b[i]+b[i+1])/K3
        l = load('b', -1); m0 = load('b', 0); h = load('b', 1)
        s1, s2, r = nid(), nid(), nid()
        L.append(f" %{s1}=fadd {fty} %{l},%{m0}")
        L.append(f" %{s2}=fadd {fty} %{s1},%{h}")
        L.append(f" %{r}=fdiv {fty} %{s2},%{ids['K3']}")
        return L, r, [('b', -1), ('b', 0), ('b', 1)]
    if kind == 'stencil5':         # a[i] = b[i-2]-b[i-1]+b[i]-b[i+1]+b[i+2]
        vs = [load('b', off) for off in (-2, -1, 0, 1, 2)]
        t1, t2, t3, r = nid(), nid(), nid(), nid()
        L.append(f" %{t1}=fsub {fty} %{vs[0]},%{vs[1]}")
        L.append(f" %{t2}=fadd {fty} %{t1},%{vs[2]}")
        L.append(f" %{t3}=fsub {fty} %{t2},%{vs[3]}")
        L.append(f" %{r}=fadd {fty} %{t3},%{vs[4]}")
        return L, r, [('b', o) for o in (-2, -1, 0, 1, 2)]
    raise AssertionError(kind)

CEXPR = {
    'map_mul_add': "b[i]*K1 + K2",
    'map_sub': "b[i] - c[i]",
    'map_mul2': "b[i] * c[i]",
    'map_div': "b[i] / c[i]",
    'map_divk': "b[i] / K3",
    'saxpy': "P*b[i] + a[i]",
    'inplace': "a[i]*a[i] + K2",
    'stencil3': "((b[i-1] + b[i]) + b[i+1]) / K3",
    'stencil5': "(((b[i-2] - b[i-1]) + b[i]) - b[i+1]) + b[i+2]",
}

def kernel_ir(kind, fty, noalias=True):
    """Emit trust_ir text for a store kernel `a[i] = TERM` over [lo, hi)."""
    stencil = kind.startswith('stencil')
    ptrs = ['a']
    if kind not in ('inplace',):
        ptrs.append('b')
    if kind in ('map_sub', 'map_mul2', 'map_div'):
        ptrs.append('c')
    has_p = kind == 'saxpy'
    params = [('%%%d' % k, 'ptr') for k in range(len(ptrs))]
    ids = {p: k for k, p in enumerate(ptrs)}
    nxt = len(ptrs)
    if has_p:
        ids['P'] = nxt; params.append(('%%%d' % nxt, fty)); nxt += 1
    ids['n'] = nxt; params.append(('%%%d' % nxt, 'i32')); nxt += 1
    consts, cid = [], nxt
    def const(name, text):
        nonlocal cid
        ids[name] = cid
        consts.append(f" %{cid}={text}")
        cid += 1
    const('c0', 'const i32 0')
    const('c1', 'const i32 1')
    const('c2', 'const i32 2')
    const('K1', f'const {fty} 2.5')
    const('K2', f'const {fty} 1.0')
    const('K3', f'const {fty} 3.0')
    lo = 'c2' if kind == 'stencil5' else ('c1' if stencil else 'c0')
    if stencil:
        # hi = n - lo  (hoisted, loop-invariant)
        ids['hi'] = cid
        consts.append(f" %{cid}=sub i32 %{ids['n']},%{ids[lo]}")
        cid += 1
        hi = 'hi'
    else:
        hi = 'n'
    ids['i'] = 90
    body, r, _loads = term_lines(kind, fty, ids)
    g = 98
    functy = ", ".join(t for _, t in params)
    bb0 = ",".join(f"%{k}: {t}" for k, (_, t) in enumerate(params))
    attr = "".join(f"; #param_attrs {k}: noalias\n" for k in range(len(ptrs))) if noalias else ""
    return f"""{HDR}functy.0 = ({functy}) -> (i32)
fn @kernel(functy.0){{
{attr}bb0({bb0}):
{chr(10).join(consts)}
 br bb1(%{ids[lo]})
bb1(%89: i32):
 %88=icmp slt i32 %89,%{ids[hi]}
 condbr %88,bb3(%89),bb2
bb3(%90: i32):
{chr(10).join(body)}
 %{g}=gep {fty},ptr %0,%90
 store {fty} %{r},ptr %{g}
 %99=add i32 %90,%{ids['c1']}
 br bb1(%99)
bb2:
 %79=const i32 0
 ret %79
}}
"""

def kernel_c(kind, fty):
    ct = 'float' if fty == 'f32' else 'double'
    lit = 'f' if fty == 'f32' else ''
    stencil = kind.startswith('stencil')
    args = [f"{ct}* a"]
    if kind != 'inplace':
        args.append(f"const {ct}* b")
    if kind in ('map_sub', 'map_mul2', 'map_div'):
        args.append(f"const {ct}* c")
    if kind == 'saxpy':
        args.append(f"{ct} P")
    args.append("int n")
    lo = '2' if kind == 'stencil5' else ('1' if stencil else '0')
    hi = f"n-{lo}" if stencil else "n"
    expr = CEXPR[kind].replace('K1', f'2.5{lit}').replace('K2', f'1.0{lit}').replace('K3', f'3.0{lit}')
    return f"""int kernel({', '.join(args)}){{
  for (int i = {lo}; i < {hi}; i++) a[i] = {expr};
  return 0;
}}
"""

def count_ir(fty):
    return f"""{HDR}functy.0 = (ptr, {fty}, i32) -> (i32)
fn @kernel(functy.0){{
bb0(%0: ptr,%1: {fty},%2: i32):
 %3=const i32 0
 %4=const i32 1
 br bb1(%3,%3)
bb1(%10: i32,%11: i32):
 %12=icmp slt i32 %10,%2
 condbr %12,bb3(%10,%11),bb2(%11)
bb3(%20: i32,%21: i32):
 %22=gep {fty},ptr %0,%20
 %23=load {fty},ptr %22
 %24=fcmp ogt {fty} %23,%1
 %25=zext bool %24 to i32
 %26=add i32 %21,%25
 %27=add i32 %20,%4
 br bb1(%27,%26)
bb2(%40: i32):
 ret %40
}}
"""

def count_c(fty):
    ct = 'float' if fty == 'f32' else 'double'
    return f"""int kernel(const {ct}* a, {ct} t, int n){{
  int c = 0;
  for (int i = 0; i < n; i++) c += (a[i] > t) ? 1 : 0;
  return c;
}}
"""

# ---------------------------------------------------------------------------
# Driver: fills arrays with the SPECIAL-VALUE mix, runs, dumps raw output.
# ---------------------------------------------------------------------------

def driver_c(kind, fty, alias=False):
    ct = 'float' if fty == 'f32' else 'double'
    ut = 'uint32_t' if fty == 'f32' else 'uint64_t'
    is_count = kind == 'count'
    # special-value table (bit patterns, per width)
    if fty == 'f32':
        specials = ("0x7fc00000u,0x7fc12345u,0x7f800001u,0xffc00000u,"      # qNaNs + sNaN pattern
                    "0x7f800000u,0xff800000u,0x00000000u,0x80000000u,"       # +-Inf, +-0
                    "0x00000001u,0x00400000u,0x007fffffu,"                   # denormals
                    "0x7f7fffffu,0x00800000u,0x3f800000u,0xbf800000u")       # MAX, MIN_NORMAL, +-1
        decl = f"static const uint32_t SPECIALS[] = {{{specials}}};"
    else:
        specials = ("0x7ff8000000000000ull,0x7ff8123456789abcull,0x7ff0000000000001ull,"
                    "0xfff8000000000000ull,0x7ff0000000000000ull,0xfff0000000000000ull,"
                    "0x0000000000000000ull,0x8000000000000000ull,"
                    "0x0000000000000001ull,0x0008000000000000ull,0x000fffffffffffffull,"
                    "0x7fefffffffffffffull,0x0010000000000000ull,"
                    "0x3ff0000000000000ull,0xbff0000000000000ull")
        decl = f"static const uint64_t SPECIALS[] = {{{specials}}};"
    ptr_args, call_args, allocs, fills = [], [], [], []
    ptrs = ['a'] if kind == 'inplace' or is_count else (
        ['a', 'b', 'c'] if kind in ('map_sub', 'map_mul2', 'map_div') else ['a', 'b'])
    for p in ptrs:
        if alias and p == 'b':
            allocs.append(f"  {ct}* b = a; /* deliberate full overlap */")
        else:
            allocs.append(f"  {ct}* {p} = ({ct}*)malloc(sizeof({ct})*(size_t)m);")
        fills.append(f"""  {{ uint64_t s = 0x9e3779b97f4a7c15ull ^ (uint64_t){ord(p)};
    for (int i = 0; i < n; i++) {{
      s = s*6364136223846793005ull + 1442695040888963407ull;
      int r = (int)((s >> 33) % 23);
      {ut} bits;
      if (r < 15) bits = SPECIALS[(i*7 + {ord(p)}) % (int)(sizeof(SPECIALS)/sizeof(SPECIALS[0]))];
      else {{ bits = ({ut})(s >> {'40' if fty == 'f32' else '12'});
             /* keep exponent moderate for finite randoms */
             bits = (bits & ~({ut}){'0x7f800000u' if fty=='f32' else '0x7ff0000000000000ull'}) | ({ut}){'0x40000000u' if fty=='f32' else '0x4000000000000000ull'}; }}
      memcpy(&{p}[i], &bits, sizeof({ct}));
    }}
  }}""")
    if is_count:
        proto = f"extern int kernel(const {ct}*, {ct}, int);"
        call = f"int res = kernel(a, ({ct})0.75, n); fwrite(&res, sizeof(res), 1, f);"
    else:
        sig = [f"{ct}*"]
        if kind != 'inplace':
            sig.append(f"const {ct}*")
        if kind in ('map_sub', 'map_mul2', 'map_div'):
            sig.append(f"const {ct}*")
        if kind == 'saxpy':
            sig.append(ct)
        sig.append("int")
        proto = f"extern int kernel({', '.join(sig)});"
        call_ptrs = ", ".join(ptrs)
        extra = f", ({ct})0.5" if kind == 'saxpy' else ""
        call = f"kernel({call_ptrs}{extra}, n); fwrite(a, sizeof({ct}), (size_t)n, f);"
    return f"""#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
{decl}
{proto}
int main(int argc, char** argv){{
  int n = atoi(argv[1]);
  int m = n > 0 ? n : 1;
{chr(10).join(allocs)}
{chr(10).join(fills)}
  FILE* f = fopen(argv[2], "wb");
  {call}
  fclose(f);
  return 0;
}}
"""

NS = [0, 1, 2, 3, 4, 7, 8, 15, 16, 17, 18, 24, 31, 32, 33, 47, 48, 63, 64, 65,
      100, 127, 128, 129, 255, 256, 257, 1000, 1023, 1024, 1027]
if QUICK:
    NS = [0, 1, 15, 16, 17, 33, 128, 1027]

KINDS = ['map_mul_add', 'map_sub', 'map_mul2', 'map_div', 'map_divk',
         'saxpy', 'inplace', 'stencil3', 'stencil5', 'count']
FTYS = ['f32', 'f64']

def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)

def compile_tcg(tir, obj, disable=None):
    env = dict(os.environ)
    if disable:
        env["TRUST_CG_DISABLE_PASSES"] = disable
    r = run([TCG, "--format=text", "--target", "aarch64", "-O2", "-c", tir, "-o", obj], env=env)
    if r.returncode != 0:
        print(r.stderr)
        raise SystemExit(f"tcg compile failed: {tir}")

def has_vec(obj):
    r = run(["objdump", "-d", obj])
    return ("st1." in r.stdout) or ("stp" in r.stdout) or ("fcmgt." in r.stdout)

def main():
    wd = tempfile.mkdtemp(prefix="fpmapfuzz")
    total = fails = 0
    vec_fired = 0
    for fty in FTYS:
        for kind in KINDS:
            name = f"{kind}_{fty}"
            tir = os.path.join(wd, name + ".trust_ir")
            cref = os.path.join(wd, name + ".c")
            drv = os.path.join(wd, name + "_drv.c")
            if kind == 'count':
                open(tir, "w").write(count_ir(fty))
                open(cref, "w").write(count_c(fty))
            else:
                open(tir, "w").write(kernel_ir(kind, fty, noalias=True))
                open(cref, "w").write(kernel_c(kind, fty))
            open(drv, "w").write(driver_c(kind, fty))
            on_o = os.path.join(wd, name + "_on.o")
            off_o = os.path.join(wd, name + "_off.o")
            compile_tcg(tir, on_o)
            compile_tcg(tir, off_o, disable="neon_fmap")
            if has_vec(on_o):
                vec_fired += 1
            else:
                print(f"NOTE: {name} did not vectorize (pass bail)")
            binaries = {}
            for tag, obj in (("on", on_o), ("off", off_o)):
                b = os.path.join(wd, name + "_" + tag)
                r = run(["clang", "-O2", drv, obj, "-o", b])
                assert r.returncode == 0, r.stderr
                binaries[tag] = b
            b = os.path.join(wd, name + "_ref")
            r = run(["clang", "-O2", "-ffp-contract=off", drv, cref, "-o", b])
            assert r.returncode == 0, r.stderr
            binaries["ref"] = b
            for n in NS:
                outs = {}
                for tag, binpath in binaries.items():
                    out = os.path.join(wd, f"{name}_{tag}_{n}.bin")
                    run([binpath, str(n), out])
                    outs[tag] = open(out, "rb").read()
                    os.unlink(out)
                total += 1
                if not (outs["on"] == outs["off"] == outs["ref"]):
                    fails += 1
                    print(f"MISMATCH {name} n={n}: on==off:{outs['on']==outs['off']} "
                          f"on==ref:{outs['on']==outs['ref']}")
    # ---- aliasing negative: two-pointer map WITHOUT noalias, overlapped ----
    for fty in FTYS:
        name = f"alias_neg_{fty}"
        tir = os.path.join(wd, name + ".trust_ir")
        open(tir, "w").write(kernel_ir('map_mul2', fty, noalias=False))
        obj = os.path.join(wd, name + ".o")
        compile_tcg(tir, obj)
        if has_vec(obj):
            fails += 1
            print(f"ALIAS-NEGATIVE FAILED: {name} vectorized WITHOUT noalias")
        drv = os.path.join(wd, name + "_drv.c")
        open(drv, "w").write(driver_c('map_mul2', fty, alias=True))
        cref = os.path.join(wd, name + ".c")
        # aliased C reference: b==a (undefined per restrict rules only if
        # restrict declared; plain pointers = well-defined, must match scalar).
        ct = 'float' if fty == 'f32' else 'double'
        open(cref, "w").write(f"""int kernel({ct}* a, const {ct}* b, const {ct}* c, int n){{
  for (int i = 0; i < n; i++) a[i] = b[i] * c[i];
  return 0;
}}
""")
        btcg = os.path.join(wd, name + "_tcg")
        bref = os.path.join(wd, name + "_ref")
        assert run(["clang", "-O2", drv, obj, "-o", btcg]).returncode == 0
        assert run(["clang", "-O2", "-ffp-contract=off", "-fno-vectorize", "-fno-slp-vectorize",
                    drv, cref, "-o", bref]).returncode == 0
        for n in (0, 1, 17, 128, 1027):
            o1 = os.path.join(wd, "t1.bin"); o2 = os.path.join(wd, "t2.bin")
            run([btcg, str(n), o1]); run([bref, str(n), o2])
            total += 1
            if open(o1, "rb").read() != open(o2, "rb").read():
                fails += 1
                print(f"ALIAS-NEGATIVE MISMATCH {name} n={n}")
    print(f"fpmapfuzz: {total - fails}/{total} bit-identical, {fails} failures; "
          f"{vec_fired}/{len(FTYS)*len(KINDS)} kernels vectorized")
    return 1 if fails else 0

if __name__ == "__main__":
    raise SystemExit(main())
