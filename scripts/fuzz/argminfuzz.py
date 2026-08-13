#!/usr/bin/env python3
"""
Soundness fuzzer for the neon-minmax INDEX-TRACKING (argmin / argmax) vectorizer.

Generates argmin/argmax loops with TWO carried accumulators (best-value +
best-index) updated under one strict min/max compare — the shape neon_minmax's
argmin path FIRES on. For each kernel it drives EVERY trip count `n` from 0
through the array length (crossing the 16-lane vector width and its tail edges)
and asserts trust-cg -O0/-O2/-O3 all agree WITH EACH OTHER and with a clang
reference — a bit-identical differential. The data is seeded with DUPLICATE min
values (first / last / adjacent / all-equal / spread), because first-occurrence
tie-breaking across lanes is the soundness crux: a miscompiling reassembly shows
up as O3 != O0 or trust-cg != clang on a duplicate-min pattern.

Also includes must-BAIL controls (non-strict `<=` select -> LAST occurrence;
index feeds back into the value term) that must stay correct (O0==O2==O3).

i64 (`.2D`) width battery: the same argmin/argmax kernels over i64/u64 values
and a 64-bit index — 8-lane blocks, so the trip counts cross the 8/16/24 edges
— with the same duplicate patterns seeded at the i64 extremes
(INT64_MIN/INT64_MAX/UINT64_MAX) plus a HIGH-BITS pattern (values differing
only above bit 32, so any 32-bit-lane confusion misfolds), and the same
must-BAIL controls at i64.

usage: argminfuzz.py <trust-cg-binary>
"""
import sys, os, subprocess, tempfile, shutil, random

# variant -> (trust_ir icmp, trust_ir i32 seed const, C value type, C seed, C cmp op)
VARIANTS = {
    'argmin_s': ('slt',  '2147483647', 'int',      '2147483647',   '<'),
    'argmax_s': ('sgt', '-2147483648', 'int',      '(-2147483647-1)', '>'),
    'argmin_u': ('ult',  '4294967295', 'unsigned', '4294967295u',  '<'),
    'argmax_u': ('ugt',  '0',          'unsigned', '0u',           '>'),
}

# i64 variant -> (icmp, trust_ir i64 seed, C value type, C seed, C cmp op)
VARIANTS64 = {
    'argmin_s64': ('slt',  '9223372036854775807', 'int64_t',
                   '9223372036854775807LL', '<'),
    'argmax_s64': ('sgt', '-9223372036854775808', 'int64_t',
                   '(-9223372036854775807LL-1)', '>'),
    'argmin_u64': ('ult', '-1', 'uint64_t', '0xFFFFFFFFFFFFFFFFULL', '<'),
    'argmax_u64': ('ugt',  '0', 'uint64_t', '0ULL', '>'),
}


def gen_tir(cmp, seed, nonstrict=False, idx_feedback=False):
    """The argmin/argmax kernel in trust_ir text.

    nonstrict: use `<=`/`>=` (LAST occurrence) — a must-BAIL control.
    idx_feedback: make the value term depend on best_idx — a must-BAIL control.
    """
    # non-strict cmp for the control: sle/sge/ule/uge.
    c = cmp
    if nonstrict:
        c = {'slt': 'sle', 'sgt': 'sge', 'ult': 'ule', 'ugt': 'uge'}[cmp]
    # value term: normally the plain load %24; for the feedback control, xor it
    # with best_idx (%22) so the term reads the index accumulator.
    if idx_feedback:
        term = "%29"
        term_insts = "    %29=xor i32 %24,%22\n"
    else:
        term = "%24"
        term_insts = ""
    return f"""; TrustIr text format v1
module "am"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, i32) -> (i32)
fn @kernel(functy.0){{
bb0(%0: ptr,%1: i32):
 %2=const i32 {seed}
 %3=const i32 0
 %4=const i32 1
 br bb1(%3,%2,%3)
bb1(%10: i32,%11: i32,%12: i32):
 %13=icmp slt i32 %10,%1
 condbr %13,bb3(%10,%11,%12),bb2(%12)
bb3(%20: i32,%21: i32,%22: i32):
 %23=gep i32,ptr %0,%20
 %24=load i32,ptr %23
{term_insts} %25=icmp {c} i32 {term},%21
 %26=select i32 %25,{term},%21
 %27=select i32 %25,%20,%22
 %28=add i32 %20,%4
 br bb1(%28,%26,%27)
bb2(%40: i32): ret %40
}}
"""


def gen_ref_c(cty, seed, cop, nonstrict=False, idx_feedback=False):
    """Matching C reference implementation of the kernel."""
    c = cop + '=' if nonstrict else cop
    v = "(unsigned)((unsigned)a[i] ^ (unsigned)bi)" if idx_feedback else f"({cty})a[i]"
    return f"""#include <stdint.h>
int kernel(const int *a, int n){{
    {cty} bv = {seed}; int bi = 0;
    for (int i = 0; i < n; i++) {{
        {cty} v = {v};
        if (v {c} bv) {{ bv = v; bi = i; }}
    }}
    return bi;
}}
"""


def gen_driver(data):
    body = ",".join(str(int(x)) for x in data)
    n = len(data)
    return f"""#include <stdio.h>
extern int kernel(const int *, int);
int main(void) {{
    static const int a[{max(n,1)}] = {{{body if n else '0'}}};
    for (int k = 0; k <= {n}; k++) printf("%d ", kernel(a, k));
    printf("\\n");
    return 0;
}}
"""


def gen_tir64(cmp, seed, nonstrict=False, idx_feedback=False):
    """The i64 (`.2D`) argmin/argmax kernel: (ptr, i64) -> (i64) best index.
    Mirrors gen_tir with all-i64 carried values and `gep i64` addressing."""
    c = cmp
    if nonstrict:
        c = {'slt': 'sle', 'sgt': 'sge', 'ult': 'ule', 'ugt': 'uge'}[cmp]
    if idx_feedback:
        term = "%29"
        term_insts = "    %29=xor i64 %24,%22\n"
    else:
        term = "%24"
        term_insts = ""
    return f"""; TrustIr text format v1
module "am64"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, i64) -> (i64)
fn @kernel(functy.0){{
bb0(%0: ptr,%1: i64):
 %2=const i64 {seed}
 %3=const i64 0
 %4=const i64 1
 br bb1(%3,%2,%3)
bb1(%10: i64,%11: i64,%12: i64):
 %13=icmp slt i64 %10,%1
 condbr %13,bb3(%10,%11,%12),bb2(%12)
bb3(%20: i64,%21: i64,%22: i64):
 %23=gep i64,ptr %0,%20
 %24=load i64,ptr %23
{term_insts} %25=icmp {c} i64 {term},%21
 %26=select i64 %25,{term},%21
 %27=select i64 %25,%20,%22
 %28=add i64 %20,%4
 br bb1(%28,%26,%27)
bb2(%40: i64): ret %40
}}
"""


def gen_ref_c64(cty, seed, cop, nonstrict=False, idx_feedback=False):
    """Matching C reference of the i64 kernel."""
    c = cop + '=' if nonstrict else cop
    v = "(uint64_t)a[i] ^ (uint64_t)bi" if idx_feedback else f"({cty})a[i]"
    return f"""#include <stdint.h>
int64_t kernel(const int64_t *a, int64_t n){{
    {cty} bv = {seed}; int64_t bi = 0;
    for (int64_t i = 0; i < n; i++) {{
        {cty} v = {v};
        if (v {c} bv) {{ bv = v; bi = i; }}
    }}
    return bi;
}}
"""


def gen_driver64(data):
    body = ",".join(f"{int(x)}LL" for x in data)
    n = len(data)
    return f"""#include <stdio.h>
#include <stdint.h>
extern int64_t kernel(const int64_t *, int64_t);
int main(void) {{
    static const int64_t a[{max(n,1)}] = {{{body if n else '0'}}};
    for (int k = 0; k <= {n}; k++) printf("%lld ", (long long)kernel(a, (int64_t)k));
    printf("\\n");
    return 0;
}}
"""


I32MIN, I32MAX, U32MAX = -2147483648, 2147483647, 4294967295
I64MIN, I64MAX = -(2**63), 2**63 - 1


def extreme(variant):
    """The dominating value for a variant (so injected duplicates are the min/max)."""
    return {'argmin_s': I32MIN, 'argmax_s': I32MAX,
            'argmin_u': 0,       'argmax_u': -1,  # -1 == 0xFFFFFFFF unsigned
            'argmin_s64': I64MIN, 'argmax_s64': I64MAX,
            'argmin_u64': 0,      'argmax_u64': -1}[variant]  # -1 == UINT64_MAX


def gen_data(rng, n, variant, pattern):
    """Random data with duplicate-extreme seedings. i64 variants draw values
    that exercise the full 64-bit range; the `high_bits` pattern makes entries
    differ ONLY above bit 32 (a 32-bit-lane confusion collapses them)."""
    is64 = variant.endswith('64')
    if is64:
        base = [(rng.randint(-50, 50) << 32) | rng.randint(0, 0xFFFF) for _ in range(n)]
    else:
        base = [rng.randint(-50, 50) for _ in range(n)]
    if n == 0:
        return base
    ex = extreme(variant)
    if pattern == 'random':
        pass
    elif pattern == 'all_equal':
        base = [7] * n
    elif pattern == 'all_extreme':
        base = [ex] * n
    elif pattern == 'first':
        base[0] = ex
    elif pattern == 'last':
        base[-1] = ex
    elif pattern == 'adjacent':
        j = rng.randint(0, max(0, n - 2))
        base[j] = ex; base[min(j + 1, n - 1)] = ex
    elif pattern == 'spread':
        for j in sorted(rng.sample(range(n), min(n, rng.randint(2, 5)))):
            base[j] = ex
    elif pattern == 'dup_nonextreme':
        # a non-extreme value repeated (min is this value, tie-break to first)
        val = rng.randint(-20, 20)
        for j in sorted(rng.sample(range(n), min(n, rng.randint(2, 6)))):
            base[j] = val
    elif pattern == 'high_bits':
        # i64-only: same low word everywhere; the ORDER lives above bit 32.
        base = [((rng.randint(1, 40) if i % 3 else rng.randint(-40, -1)) << 32) | 0xABCD
                for i in range(n)]
    return base


def run_bin(path):
    return subprocess.run([path], capture_output=True, text=True).stdout.strip()


def compile_trustcg(tcg, tir, o, wd, tag):
    obj = os.path.join(wd, f"{tag}.o")
    r = subprocess.run([tcg, "--format=text", "--target", "aarch64", f"-{o}", "-c", tir, "-o", obj],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return None, (r.stderr or r.stdout).strip().splitlines()[-1:] or ['?']
    return obj, None


def main():
    if len(sys.argv) < 2:
        print("usage: argminfuzz.py <trust-cg-binary>"); sys.exit(2)
    tcg = sys.argv[1]
    rng = random.Random(0xA26311)
    wd = tempfile.mkdtemp(prefix="argminfuzz_")
    # trip-count edges around the 16-lane width and its multiples/tails.
    LENS = [0, 1, 2, 3, 4, 15, 16, 17, 18, 19, 31, 32, 33, 47, 48, 49, 64, 65, 80, 100, 129]
    PATTERNS = ['random', 'all_equal', 'all_extreme', 'first', 'last',
                'adjacent', 'spread', 'dup_nonextreme']
    OLEVELS = ['O0', 'O2', 'O3']

    ok = mism = err = 0
    fails = []
    idx = 0
    for variant, (icmp, seed, cty, cseed, cop) in VARIANTS.items():
        tir = os.path.join(wd, f"{variant}.trust_ir")
        open(tir, "w").write(gen_tir(icmp, seed))
        refc = os.path.join(wd, f"{variant}_ref.c")
        open(refc, "w").write(gen_ref_c(cty, cseed, cop))
        # compile the kernel once per O-level (data lives in the driver).
        objs = {}
        cerr = False
        for o in OLEVELS:
            obj, e = compile_trustcg(tcg, tir, o, wd, f"{variant}_{o}")
            if obj is None:
                err += 1; fails.append((f"{variant} compile -{o}", e)); cerr = True; break
            objs[o] = obj
        if cerr:
            continue
        for L in LENS:
            for pat in PATTERNS:
                idx += 1
                data = gen_data(rng, L, variant, pat)
                drv = os.path.join(wd, f"d{idx}.c")
                open(drv, "w").write(gen_driver(data))
                outs = {}
                linkerr = False
                for o in OLEVELS:
                    b = os.path.join(wd, f"b{idx}_{o}")
                    if subprocess.run(["cc", drv, objs[o], "-o", b],
                                      capture_output=True).returncode != 0:
                        err += 1; fails.append((f"{variant}/{pat}/n<= {L} link -{o}", [])); linkerr = True; break
                    outs[o] = run_bin(b)
                if linkerr:
                    continue
                # clang reference
                cb = os.path.join(wd, f"c{idx}")
                subprocess.run(["cc", "-O3", refc, drv, "-o", cb], capture_output=True)
                outs['clang'] = run_bin(cb)
                vals = set(outs.values())
                if len(vals) == 1:
                    ok += 1
                else:
                    mism += 1
                    fails.append((f"{variant}/{pat}/n<= {L}", outs, data))

    # ---------------------------------------------------------------------
    # i64 (`.2D`) width battery: 8-lane blocks, i64 extremes, high-bits
    # ordering, same duplicate patterns, plus FIRE pins on the -O2/-O3 objects.
    # ---------------------------------------------------------------------
    LENS64 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 23, 24, 25,
              31, 32, 33, 63, 64, 65, 100]
    PATTERNS64 = PATTERNS + ['high_bits']
    idx64 = 0
    for variant, (icmp, seed, cty, cseed, cop) in VARIANTS64.items():
        tir = os.path.join(wd, f"{variant}.trust_ir")
        open(tir, "w").write(gen_tir64(icmp, seed))
        refc = os.path.join(wd, f"{variant}_ref.c")
        open(refc, "w").write(gen_ref_c64(cty, cseed, cop))
        objs = {}
        cerr = False
        for o in OLEVELS:
            obj, e = compile_trustcg(tcg, tir, o, wd, f"{variant}_{o}")
            if obj is None:
                err += 1; fails.append((f"{variant} compile -{o}", e)); cerr = True; break
            objs[o] = obj
        if cerr:
            continue
        # FIRE pin: the .2D compare + BIT dual-select must be in the O2/O3
        # objects (signed -> cmgt.2d, unsigned -> cmhi.2d), never in O0.
        want_cmp = "cmgt.2d" if variant.endswith('_s64') else "cmhi.2d"
        for o, expect in [("O0", False), ("O2", True), ("O3", True)]:
            dis = subprocess.run(["otool", "-tvV", objs[o]],
                                 capture_output=True, text=True).stdout.lower()
            got = (want_cmp in dis) and ("bit.16b" in dis)
            if got != expect:
                err += 1
                fails.append((f"{variant} FIRE pin -{o}: {want_cmp}+bit expected={expect} got={got}", []))
        for L in LENS64:
            for pat in PATTERNS64:
                idx64 += 1
                data = gen_data(rng, L, variant, pat)
                drv = os.path.join(wd, f"d64_{idx64}.c")
                open(drv, "w").write(gen_driver64(data))
                outs = {}
                linkerr = False
                for o in OLEVELS:
                    b = os.path.join(wd, f"b64_{idx64}_{o}")
                    if subprocess.run(["cc", drv, objs[o], "-o", b],
                                      capture_output=True).returncode != 0:
                        err += 1; fails.append((f"{variant}/{pat}/n<= {L} link -{o}", [])); linkerr = True; break
                    outs[o] = run_bin(b)
                if linkerr:
                    continue
                cb = os.path.join(wd, f"c64_{idx64}")
                subprocess.run(["cc", "-O3", refc, drv, "-o", cb], capture_output=True)
                outs['clang'] = run_bin(cb)
                vals = set(outs.values())
                if len(vals) == 1:
                    ok += 1
                else:
                    mism += 1
                    fails.append((f"{variant}/{pat}/n<= {L}", outs, data))

    # must-BAIL controls: non-strict select (LAST occurrence) + index feedback.
    # These must stay CORRECT (trust-cg must not apply first-occurrence argmin to
    # a last-occurrence loop); we check O0==O2==O3==clang-of-the-same-semantics.
    # Run at BOTH widths — the strictness/feedback gates are width-independent.
    ctrl_idx = 0
    all_variants = [(v, sp, False) for v, sp in VARIANTS.items()] + \
                   [(v, sp, True) for v, sp in VARIANTS64.items()]
    for variant, (icmp, seed, cty, cseed, cop), is64 in all_variants:
        for ctrl in ('nonstrict', 'idx_feedback'):
            ns = ctrl == 'nonstrict'; fb = ctrl == 'idx_feedback'
            tir = os.path.join(wd, f"ctrl_{variant}_{ctrl}.trust_ir")
            gen_t = gen_tir64 if is64 else gen_tir
            gen_r = gen_ref_c64 if is64 else gen_ref_c
            gen_d = gen_driver64 if is64 else gen_driver
            open(tir, "w").write(gen_t(icmp, seed, nonstrict=ns, idx_feedback=fb))
            refc = os.path.join(wd, f"ctrl_{variant}_{ctrl}_ref.c")
            open(refc, "w").write(gen_r(cty, cseed, cop, nonstrict=ns, idx_feedback=fb))
            objs = {}; bad = False
            for o in OLEVELS:
                obj, e = compile_trustcg(tcg, tir, o, wd, f"ctrl_{variant}_{ctrl}_{o}")
                if obj is None:
                    err += 1; fails.append((f"CTRL {variant}/{ctrl} compile -{o}", e)); bad = True; break
                objs[o] = obj
            if bad:
                continue
            ctrl_lens = [0, 5, 8, 9, 17, 33] if is64 else [0, 5, 16, 17, 33, 65]
            for L in ctrl_lens:
                for pat in ['random', 'all_extreme', 'spread', 'dup_nonextreme']:
                    ctrl_idx += 1
                    data = gen_data(rng, L, variant, pat)
                    drv = os.path.join(wd, f"cd{ctrl_idx}.c")
                    open(drv, "w").write(gen_d(data))
                    outs = {}
                    for o in OLEVELS:
                        b = os.path.join(wd, f"cb{ctrl_idx}_{o}")
                        subprocess.run(["cc", drv, objs[o], "-o", b], capture_output=True)
                        outs[o] = run_bin(b)
                    cb = os.path.join(wd, f"cc{ctrl_idx}")
                    subprocess.run(["cc", "-O3", refc, drv, "-o", cb], capture_output=True)
                    outs['clang'] = run_bin(cb)
                    if len(set(outs.values())) == 1:
                        ok += 1
                    else:
                        mism += 1
                        fails.append((f"CTRL {variant}/{ctrl}/{pat}/n<= {L}", outs, data))

    print(f"\n=== argmin/argmax index-tracking soundness: {idx} i32 + {idx64} i64 "
          f"+ {ctrl_idx} control kernels ===")
    print(f"OK(O0==O2==O3==clang)={ok}  MISMATCH={mism}  other(compile/link)={err}")
    if fails:
        print(f"\n!!! {len(fails)} FAILURES:")
        for f in fails[:25]:
            print("   ", f[0], "->", f[1] if len(f) > 1 else "")
            if len(f) > 2:
                print("       data:", f[2])
    shutil.rmtree(wd, ignore_errors=True)
    sys.exit(1 if (mism or err) else 0)


if __name__ == "__main__":
    main()
