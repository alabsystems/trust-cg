#!/usr/bin/env python3
"""
Soundness fuzzer for the neon-find EARLY-EXIT linear-search vectorizer.

Generates the first-match `find` kernel

    for (i = 0; i < n; i++) if (a[i] == key) return i;
    return -1;

— the shape neon-find FIRES on — and, for a battery of match positions
(none / first / middle / last / same-block-duplicate / cross-block-duplicate)
crossed with trip counts `n` sweeping every edge around the 16-lane block width
and its tails, asserts that trust-cg -O0, -O2, -O3, -O3-with-neon-find-DISABLED,
and a clang -O3 reference ALL agree — a bit-identical `on == off == clang`
differential.

The soundness crux is the vector loop's over-read (it reads whole 16-element
blocks even when the scalar loop would have exited mid-block) and the
first-match-across-lanes semantics (delegated to the scalar loop, which re-scans
the matching block from its base). A miscompiling reassembly — a skipped
matching block, a wrong first-match index, or an out-of-bounds fault on a tail —
shows up as O3 != O0/off or trust-cg != clang on a duplicate / tail pattern.

BYTE (`memchr`, .16B) width battery: the same first-match kernel over u8 with
64-byte blocks — the same duplicate/tail patterns at 64-block granularity, PLUS
  * a KEY-OVERFLOW adversarial case (key = 346 > 255 with trunc8(key) = 0x5A
    bytes planted): the scalar never matches, so the vector byte filter's
    false-POSITIVE hits must still return -1 (superset-filter direction pin);
  * FIRE/BAIL pins: the O3 object must contain cmeq.16b, the disabled one none;
  * GUARD-PAGE reads on BOTH widths: element n sits at a PROT_NONE page, so any
    vector read past the scalar loop's [0,n) worst-case read set faults — the
    over-read-subset crux pinned natively.

usage: findfuzz.py <trust-cg-binary>
"""
import sys, os, subprocess, tempfile, shutil, random

KEY = 999  # the searched-for sentinel (kept out of the random filler range)
BKEY = 0x5A  # byte-width sentinel (filler range excludes it)
BKEY_OVERFLOW = 0x15A  # 346: > 255, trunc8 == BKEY — scalar can never match


def gen_tir():
    """The find kernel in trust_ir text: (ptr a, i32 n, i32 key) -> i32 index."""
    return """; TrustIr text format v1
module "find"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, i32, i32) -> (i32)
fn @findkey(functy.0){
bb0(%0: ptr,%1: i32,%2: i32):
 %3=const i32 0
 %4=const i32 1
 %5=const i32 -1
 br bb1(%3)
bb1(%10: i32):
 %11=icmp slt i32 %10,%1
 condbr %11,bb2(%10),bb4()
bb2(%20: i32):
 %21=gep i32,ptr %0,%20
 %22=load i32,ptr %21
 %23=icmp eq i32 %22,%2
 condbr %23,bb3(%20),bb5(%20)
bb3(%30: i32): ret %30
bb5(%40: i32):
 %41=add i32 %40,%4
 br bb1(%41)
bb4(): ret %5
}
"""


def gen_ref_c():
    return """#include <stdint.h>
int findkey(const int *a, int n, int key){
    for (int i = 0; i < n; i++) if (a[i] == key) return i;
    return -1;
}
"""


def gen_tir_byte():
    """The BYTE find kernel: (ptr a_u8, i32 n, i32 key) -> i32 index.
    The loaded term is `zext i8 -> i32` — the Uxtb(LdrbRI) widening shape."""
    return """; TrustIr text format v1
module "findb"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, i32, i32) -> (i32)
fn @findbyte(functy.0){
bb0(%0: ptr,%1: i32,%2: i32):
 %3=const i32 0
 %4=const i32 1
 %5=const i32 -1
 br bb1(%3)
bb1(%10: i32):
 %11=icmp slt i32 %10,%1
 condbr %11,bb2(%10),bb4()
bb2(%20: i32):
 %21=gep i8,ptr %0,%20
 %22=load i8,ptr %21
 %25=zext i8 %22 to i32
 %23=icmp eq i32 %25,%2
 condbr %23,bb3(%20),bb5(%20)
bb3(%30: i32): ret %30
bb5(%40: i32):
 %41=add i32 %40,%4
 br bb1(%41)
bb4(): ret %5
}
"""


def gen_ref_c_byte():
    return """#include <stdint.h>
int findbyte(const unsigned char *a, int n, int key){
    for (int i = 0; i < n; i++) if ((int)a[i] == key) return i;
    return -1;
}
"""


def gen_driver_byte(data, ns, key):
    body = ",".join(str(int(x)) for x in data)
    n = len(data)
    nlist = ",".join(str(x) for x in ns)
    return f"""#include <stdio.h>
extern int findbyte(const unsigned char *, int, int);
int main(void) {{
    static const unsigned char a[{max(n,1)}] = {{{body if n else '0'}}};
    static const int ns[] = {{{nlist}}};
    for (unsigned k = 0; k < sizeof(ns)/sizeof(ns[0]); k++)
        printf("%d ", findbyte(a, ns[k], {key}));
    printf("\\n");
    return 0;
}}
"""


# Guard-page driver: element n of `a` abuts a PROT_NONE page — any read past
# the scalar loop's [0,n) worst-case read set faults (over-read-subset pin).
GUARD_DRIVER = """#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
extern int {fn}(const {ety} *, int, int);
static {ety}* guarded(int n){{
  long pg=sysconf(_SC_PAGESIZE); size_t need=(size_t)(n>0?n:1)*sizeof({ety});
  size_t pages=(need+pg-1)/pg, total=(pages+1)*pg;
  char* base=mmap(0,total,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANON,-1,0);
  if(base==MAP_FAILED){{perror("mmap");exit(3);}}
  mprotect(base+pages*pg,pg,PROT_NONE);
  return ({ety}*)(base+pages*pg-need);
}}
int main(int argc,char**argv){{
  int n=atoi(argv[1]); int pat=atoi(argv[2]);
  {ety}* a=guarded(n);
  for(int i=0;i<n;i++) a[i]=({ety})(i%37+1); /* never the key */
  /* pat 0: no match; 1: match at n-1 (last legal read); 2: match mid. */
  if(n>0&&pat==1) a[n-1]=({ety}){key};
  if(n>2&&pat==2) a[n/2]=({ety}){key};
  printf("%d\\n", {fn}(a,n,{key}));
  return 0;
}}
"""


def fired(obj, needle):
    dis = subprocess.run(["otool", "-tvV", obj], capture_output=True, text=True).stdout.lower()
    return needle in dis


def gen_driver(data, ns):
    body = ",".join(str(int(x)) for x in data)
    n = len(data)
    nlist = ",".join(str(x) for x in ns)
    return f"""#include <stdio.h>
extern int findkey(const int *, int, int);
int main(void) {{
    static const int a[{max(n,1)}] = {{{body if n else '0'}}};
    static const int ns[] = {{{nlist}}};
    for (unsigned k = 0; k < sizeof(ns)/sizeof(ns[0]); k++)
        printf("%d ", findkey(a, ns[k], {KEY}));
    printf("\\n");
    return 0;
}}
"""


def filler(n, rng):
    """Random data that never equals KEY."""
    return [rng.randint(-40, 40) for _ in range(n)]


def plant(base, positions):
    for p in positions:
        if 0 <= p < len(base):
            base[p] = KEY
    return base


def gen_data(rng, N, pattern, key=KEY, blk_w=16, fill=None):
    """Full-length array (length N) seeded with `key` per the match pattern.
    `blk_w` is the vector block width (16 i32 elements / 64 bytes); the
    duplicate patterns place matches at that granularity."""
    base = fill(N, rng) if fill else filler(N, rng)
    if N == 0:
        return base
    def plant_k(positions):
        for p in positions:
            if 0 <= p < len(base):
                base[p] = key
    if pattern == 'none':
        pass
    elif pattern == 'first':
        plant_k([0])
    elif pattern == 'middle':
        plant_k([N // 2])
    elif pattern == 'last':
        plant_k([N - 1])
    elif pattern == 'dup_same_block':
        # two matches inside one vector block
        blk = rng.randint(0, max(0, (N - 1) // blk_w)) * blk_w
        plant_k([blk + 2, blk + blk_w // 2 + 1])
    elif pattern == 'dup_cross_block':
        # matches in two different blocks (first must win)
        plant_k([rng.randint(0, min(N - 1, blk_w - 1)),
                 rng.randint(min(N - 1, blk_w), N - 1)])
    elif pattern == 'spread':
        for j in sorted(rng.sample(range(N), min(N, rng.randint(2, 6)))):
            base[j] = key
    elif pattern == 'early':
        plant_k([rng.randint(0, min(N - 1, 4))])
    return base


def byte_filler(n, rng):
    """Random u8 data that never equals BKEY."""
    out = []
    for _ in range(n):
        v = rng.randint(0, 255)
        while v == BKEY:
            v = rng.randint(0, 255)
        out.append(v)
    return out


def compile_obj(tcg, tir, o, wd, tag, disable_find=False):
    obj = os.path.join(wd, f"{tag}.o")
    env = dict(os.environ)
    if disable_find:
        env["TRUST_CG_DISABLE_PASSES"] = "neon_find"
    r = subprocess.run(
        [tcg, "--format=text", "--target", "aarch64", f"-{o}", "-c", tir, "-o", obj],
        capture_output=True, text=True, env=env)
    if r.returncode != 0:
        return None, (r.stderr or r.stdout).strip().splitlines()[-1:] or ['?']
    return obj, None


def run_bin(path):
    return subprocess.run([path], capture_output=True, text=True).stdout.strip()


def main():
    if len(sys.argv) < 2:
        print("usage: findfuzz.py <trust-cg-binary>"); sys.exit(2)
    tcg = sys.argv[1]
    rng = random.Random(0xF17D)
    wd = tempfile.mkdtemp(prefix="findfuzz_")

    N = 160
    # trip-count edges around the 16-lane width, its multiples, and tails.
    NS = [0, 1, 2, 3, 4, 15, 16, 17, 18, 19, 31, 32, 33, 47, 48, 49,
          64, 65, 79, 80, 96, 111, 128, 129, 159, 160]
    PATTERNS = ['none', 'first', 'middle', 'last', 'dup_same_block',
                'dup_cross_block', 'spread', 'early']

    tir = os.path.join(wd, "find.trust_ir")
    open(tir, "w").write(gen_tir())
    refc = os.path.join(wd, "find_ref.c")
    open(refc, "w").write(gen_ref_c())

    # Compile the kernel once per variant (the data lives in the driver).
    variants = {
        'O0': ('O0', False),
        'O2': ('O2', False),
        'O3': ('O3', False),
        'O3off': ('O3', True),  # neon-find DISABLED -> the scalar reference
    }
    objs = {}
    for name, (olvl, dis) in variants.items():
        obj, e = compile_obj(tcg, tir, olvl, wd, name, disable_find=dis)
        if obj is None:
            print(f"!!! compile {name} failed: {e}"); shutil.rmtree(wd, True); sys.exit(1)
        objs[name] = obj

    ok = mism = err = 0
    fails = []
    idx = 0
    for trial in range(6):
        for pat in PATTERNS:
            idx += 1
            data = gen_data(rng, N, pat)
            drv = os.path.join(wd, f"d{idx}.c")
            open(drv, "w").write(gen_driver(data, NS))
            outs = {}
            linkerr = False
            for name in variants:
                b = os.path.join(wd, f"b{idx}_{name}")
                if subprocess.run(["cc", drv, objs[name], "-o", b],
                                  capture_output=True).returncode != 0:
                    err += 1; fails.append((f"{pat}/t{trial} link {name}", [])); linkerr = True; break
                outs[name] = run_bin(b)
            if linkerr:
                continue
            cb = os.path.join(wd, f"c{idx}")
            subprocess.run(["cc", "-O3", refc, drv, "-o", cb], capture_output=True)
            outs['clang'] = run_bin(cb)
            if len(set(outs.values())) == 1:
                ok += 1
            else:
                mism += 1
                fails.append((f"{pat}/t{trial}", outs))

    # ---------------------------------------------------------------------
    # BYTE (`memchr`, .16B) width battery: 64-byte blocks, same adversarial
    # patterns at 64-block granularity, key-overflow superset-filter pin,
    # fire/bail pins, and guard-page reads on both widths.
    # ---------------------------------------------------------------------
    NB = 320
    # trip-count edges around the 64-byte block width, its multiples, and tails.
    NSB = [0, 1, 2, 3, 15, 16, 17, 63, 64, 65, 66, 127, 128, 129,
           191, 192, 193, 255, 256, 257, 319, 320]

    btir = os.path.join(wd, "findb.trust_ir")
    open(btir, "w").write(gen_tir_byte())
    brefc = os.path.join(wd, "findb_ref.c")
    open(brefc, "w").write(gen_ref_c_byte())

    bobjs = {}
    for name, (olvl, dis) in variants.items():
        obj, e = compile_obj(tcg, btir, olvl, wd, f"byte_{name}", disable_find=dis)
        if obj is None:
            print(f"!!! compile byte {name} failed: {e}"); shutil.rmtree(wd, True); sys.exit(1)
        bobjs[name] = obj

    # FIRE/BAIL pins: cmeq.16b in the O3 object, none when disabled.
    if not fired(bobjs['O3'], "cmeq.16b"):
        print("!!! FIRE pin: byte find at -O3 did not emit cmeq.16b"); err += 1
    if fired(bobjs['O3off'], "cmeq.16b"):
        print("!!! BAIL pin: disabled byte find still emitted cmeq.16b"); err += 1
    # i32 fire pin stays .4S.
    if not fired(objs['O3'], "cmeq.4s"):
        print("!!! FIRE pin: i32 find at -O3 did not emit cmeq.4s"); err += 1

    bidx = 0
    # (battery key, planted key) — the overflow battery plants trunc8(key)
    # bytes so the vector filter false-positives while the scalar never
    # matches (every trip count must return -1).
    for bat_key, plant_key in [(BKEY, BKEY), (BKEY_OVERFLOW, BKEY)]:
        for trial in range(4):
            for pat in PATTERNS:
                bidx += 1
                data = gen_data(rng, NB, pat, key=plant_key, blk_w=64, fill=byte_filler)
                drv = os.path.join(wd, f"bd{bidx}.c")
                open(drv, "w").write(gen_driver_byte(data, NSB, bat_key))
                outs = {}
                linkerr = False
                for name in variants:
                    b = os.path.join(wd, f"bb{bidx}_{name}")
                    if subprocess.run(["cc", drv, bobjs[name], "-o", b],
                                      capture_output=True).returncode != 0:
                        err += 1; fails.append((f"byte/{pat}/k{bat_key}/t{trial} link {name}", []))
                        linkerr = True; break
                    outs[name] = run_bin(b)
                if linkerr:
                    continue
                cb = os.path.join(wd, f"bc{bidx}")
                subprocess.run(["cc", "-O3", brefc, drv, "-o", cb], capture_output=True)
                outs['clang'] = run_bin(cb)
                if len(set(outs.values())) == 1:
                    ok += 1
                else:
                    mism += 1
                    fails.append((f"byte/{pat}/k{bat_key}/t{trial}", outs))

    # ---- GUARD-PAGE reads: [0,n) exactly, both widths, O3 (pass ON). ----
    guards = 0
    for tag, fn, ety, key, obj, gns in [
        ("i32", "findkey", "int", KEY, objs['O3'],
         [0, 1, 15, 16, 17, 31, 33, 48, 129, 160]),
        ("byte", "findbyte", "unsigned char", BKEY, bobjs['O3'],
         [0, 1, 63, 64, 65, 127, 129, 192, 320, 1000]),
    ]:
        gdrv = os.path.join(wd, f"guard_{tag}.c")
        open(gdrv, "w").write(GUARD_DRIVER.format(fn=fn, ety=ety, key=key))
        gbin = os.path.join(wd, f"guard_{tag}")
        if subprocess.run(["cc", gdrv, obj, "-o", gbin], capture_output=True).returncode != 0:
            err += 1; fails.append((f"guard/{tag} link", [])); continue
        for n in gns:
            for pat in (0, 1, 2):
                guards += 1
                r = subprocess.run([gbin, str(n), str(pat)], capture_output=True, text=True)
                want = "-1" if (pat == 0 or n == 0 or (pat == 2 and n <= 2)) else \
                       (str(n - 1) if pat == 1 else str(n // 2))
                got = r.stdout.strip()
                if r.returncode != 0:
                    mism += 1; fails.append((f"guard/{tag} n={n} pat={pat} FAULT rc={r.returncode}", []))
                elif got != want:
                    mism += 1; fails.append((f"guard/{tag} n={n} pat={pat}", {"got": got, "want": want}))
                else:
                    ok += 1

    total = idx + bidx + guards
    print(f"\n=== neon-find early-exit search soundness: {idx} i32 kernels x {len(NS)} trips"
          f" + {bidx} byte kernels x {len(NSB)} trips + {guards} guard-page runs ===")
    print(f"OK(O0==O2==O3==O3off==clang)={ok}  MISMATCH={mism}  other(compile/link)={err}")
    if fails:
        print(f"\n!!! {len(fails)} FAILURES:")
        for f in fails[:20]:
            print("   ", f[0], "->", f[1])
    shutil.rmtree(wd, ignore_errors=True)
    sys.exit(1 if (mism or err) else 0)


if __name__ == "__main__":
    main()
