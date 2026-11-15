"""Exhaustive sweep of the W-bit analog (H = W/2 limbs) without numpy, W in {8, 16}.

For each a (one row) every b is evaluated at once: per-lane values are packed into one
Python int (SWAR lanes: 32-bit lanes for W-bit values and products, 16-bit lanes for
H-bit sums/compares, 8-bit lanes for booleans), and H-bit limb multiplies with a scalar
operand are bytes.translate table lookups. Every row covers all 2^W values of b, so a run
covers all 2^(2W) pairs (2^32 at W = 16).

Specs, two independent spellings each, cross-checked on every row:
  unsigned: (a * b) >> W != 0 from the packed true product; and b > (2^W-1)//a.
  signed:   biased packed true product Q = a*b + 2^31 out of [2^31-2^(W-1), 2^31+2^(W-1));
            and the closed-form interval of b with a*b in range.

Modes:
  u | s          full sweep of the unsigned / signed expansion plus its mutants
  xcheck-u|s K   compare every flag of K rows (special + random) with lir_model.Conc
"""
import json
import random
import sys
import time
from array import array

from lir_model import Conc, S_MUTANTS, U_MUTANTS, smulo_new, umulo_new

W = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[1] in ("u", "s") else 16
if sys.argv[1].startswith("xcheck"):
    W = int(sys.argv[3]) if len(sys.argv) > 3 else 16
H = W // 2
N = 1 << W
MW, MH = (1 << W) - 1, (1 << H) - 1
HALF = 1 << (W - 1)

assert array("I").itemsize == 4 and sys.byteorder == "little"
REP32 = int.from_bytes(b"\x01\x00\x00\x00" * N, "little")
REP16 = int.from_bytes(b"\x01\x00" * N, "little")
ZERO8 = bytes(N)


def sx(x, w):
    return x - (1 << w) if x >> (w - 1) else x


def l16(bs):
    buf = bytearray(2 * N)
    buf[0::2] = bs
    return int.from_bytes(buf, "little")


def l32(bs):
    buf = bytearray(4 * N)
    buf[0::4] = bs
    return int.from_bytes(buf, "little")


def l32_byte0(x):
    return x.to_bytes(4 * N, "little")[0::4]


def l16_byte0(x):
    return x.to_bytes(2 * N, "little")[0::2]


def b8(bs):
    return int.from_bytes(bs, "little")


# H-bit limb tables (index = the per-lane limb, table chosen by the scalar limb)
LO = [bytes(((x * y) & MH) if y <= MH else 0 for y in range(256)) for x in range(MH + 1)]
HNZ = [bytes((1 if (x * y) >> H else 0) if y <= MH else 0 for y in range(256))
       for x in range(MH + 1)]
SOVF = [bytes((0 if -(1 << (H - 1)) <= sx(x, H) * sx(y, H) < (1 << (H - 1)) else 1)
              if y <= MH else 0 for y in range(256)) for x in range(MH + 1)]
NZ_TABLE = bytes(1 if y else 0 for y in range(256))
FLIP = bytes((y ^ 1) if y < 2 else y for y in range(256))

PB32 = int.from_bytes(array("I", range(N)).tobytes(), "little")
PBS = int.from_bytes(array("I", (b ^ HALF for b in range(N))).tobytes(), "little")
PBN = int.from_bytes(array("I", (MW - (b ^ HALF) for b in range(N))).tobytes(), "little")
B0 = bytes(b & MH for b in range(N))
B1 = bytes(b >> H for b in range(N))
B1NZ = B1.translate(NZ_TABLE)
SB = bytes(b >> (W - 1) for b in range(N))
UBV = [abs(sx(b, W)) & MW for b in range(N)]
UB0 = bytes(u & MH for u in UBV)
UB1 = bytes(u >> H for u in UBV)
UB1NZ = UB1.translate(NZ_TABLE)
MW32, MH32, MH16 = MW * REP32, MH * REP32, MH * REP16
G16 = (1 << H) * REP16
SGN16 = (1 << (H - 1)) * REP16


def spec_u(prod):
    x = (prod >> W) & MW32
    return b8(l32_byte0(((x + MW32) >> W) & REP32))


def spec_u_threshold(a):
    if a == 0:
        return 0
    k = min(MW // a, N - 1)
    return b8(bytes(k + 1) + b"\x01" * (N - k - 1))


def spec_s(a):
    sa_ = sx(a, W)
    if sa_ >= 0:
        q = sa_ * PBS + ((1 << 31) - HALF * sa_) * REP32
    else:
        n = -sa_
        q = n * PBN + ((1 << 31) - (HALF - 1) * n) * REP32
    top = 32 - W
    v = ((q + HALF * REP32) >> W) & (((1 << top) - 1) * REP32)
    x = v ^ ((1 << (31 - W)) * REP32)
    return b8(l32_byte0(((x + ((1 << top) - 1) * REP32) >> top) & REP32))


def spec_s_threshold(a):
    s = sx(a, W)
    if s == 0:
        return 0
    lo_v, hi_v = -HALF, HALF - 1
    if s > 0:
        blo, bhi = -((-lo_v) // s), hi_v // s  # ceil(lo/s), floor(hi/s)
    else:
        blo, bhi = -((-hi_v) // s), lo_v // s  # ceil(hi/s), floor(lo/s)
    blo, bhi = max(blo, -HALF), min(bhi, HALF - 1)
    signed_order = b"\x01" * (blo + HALF) + bytes(bhi - blo + 1) + b"\x01" * (HALF - 1 - bhi)
    assert len(signed_order) == N
    return b8(signed_order[HALF:] + signed_order[:HALF])  # pattern order: 0.., then negatives


def ult16(x16, y16):
    """lane bit0 = x < y for H-bit lanes."""
    ge = (((x16 + G16) - y16) >> H) & REP16
    return l16_byte0(ge ^ REP16)


def core(x0, x1, Y0, Y1, Y1NZ, P1, m=None):
    """u_core with scalar x limbs and per-lane y limbs / product high limb P1 (bytes)."""
    if m == "smul_cross":
        O1, O2 = Y0.translate(SOVF[x1]), Y1.translate(SOVF[x0])
    else:
        O1, O2 = Y0.translate(HNZ[x1]), Y1.translate(HNZ[x0])
    M1, M2 = Y0.translate(LO[x1]), Y1.translate(LO[x0])
    if m == "t_or":
        T = l16(M1) | l16(M2)
    else:
        T = (l16(M1) + l16(M2)) & MH16
    P = l16(P1)
    if m == "carry_signed":
        C = ult16(P ^ SGN16, T ^ SGN16)
    elif m == "carry_ule":
        C = l16_byte0(((((T + G16) - P) >> H) & REP16))  # t >= p  <=>  p <= t
    else:
        C = ult16(P, T)
    BOTH = Y1NZ if x1 != 0 else ZERO8
    terms = {"o1": b8(O1), "o2": b8(O2), "c": b8(C), "both": b8(BOTH)}
    drop = {"drop_carry": "c", "drop_both": "both", "drop_o1": "o1", "drop_o2": "o2"}.get(m)
    acc = 0
    for k, v in terms.items():
        if k != drop:
            acc |= v
    return acc


def row_u(a):
    prod = a * PB32
    r1 = l32_byte0((prod >> H) & MH32)
    a0, a1 = a & MH, a >> H
    out = {"u.new": core(a0, a1, B0, B1, B1NZ, r1)}
    for m in U_MUTANTS:
        out[f"u.mut.{m}"] = core(a0, a1, B0, B1, B1NZ, r1, m)
    return prod, out


def row_s(a, prod):
    r = prod & MW32
    sa = a >> (W - 1)
    ua = abs(sx(a, W)) & MW
    ua0, ua1 = ua & MH, ua >> H
    NEG = SB.translate(FLIP) if sa else SB

    def pu1_for(negbytes):
        n32 = l32(negbytes)
        pu = ((r ^ (n32 * MW)) + n32) & MW32
        return l32_byte0((pu >> H) & MH32)

    rneg = b8(l32_byte0((r >> (W - 1)) & REP32))
    rnz = b8(l32_byte0(((r + MW32) >> W) & REP32))
    neg8 = b8(NEG)
    ou = core(ua0, ua1, UB0, UB1, UB1NZ, pu1_for(NEG))
    bad = (rneg ^ neg8) & rnz
    out = {"s.new": ou | bad,
           "s.mut.no_zero_guard": ou | (rneg ^ neg8),
           "s.mut.no_sign_check": ou,
           "s.mut.no_ou": bad}
    NEG_OR = b"\x01" * N if sa else SB
    nor8 = b8(NEG_OR)
    out["s.mut.neg_or"] = core(ua0, ua1, UB0, UB1, UB1NZ, pu1_for(NEG_OR)) | (
        (rneg ^ nor8) & rnz)
    r1 = l32_byte0((r >> H) & MH32)
    out["s.mut.pu_eq_r"] = core(ua0, ua1, UB0, UB1, UB1NZ, r1) | bad
    out["s.mut.unsigned_core_raw"] = core(a & MH, a >> H, B0, B1, B1NZ, r1) | bad
    return out


def run(mode):
    t0 = time.process_time()
    tally = {}
    spec_disagree = 0
    for a in range(N):
        prod, out_u = row_u(a) if mode == "u" else (a * PB32, None)
        su, ss = spec_u(prod), spec_s(a)
        if su != spec_u_threshold(a) or ss != spec_s_threshold(a):
            spec_disagree += 1
        if mode == "u":
            items = [(k, v, su) for k, v in out_u.items()]
            items.append(("s.mut.dispatch_swap(u-expansion)", out_u["u.new"], ss))
        else:
            out_s = row_s(a, prod)
            items = [(k, v, ss) for k, v in out_s.items()]
            items.append(("u.mut.dispatch_swap(s-expansion)", out_s["s.new"], su))
        for k, v, spec in items:
            d = (v ^ spec).bit_count()
            e = tally.setdefault(k, {"mismatches": 0, "first_a": None})
            e["mismatches"] += d
            if d and e["first_a"] is None:
                e["first_a"] = a
    tally["_spec_spellings_disagree_rows"] = spec_disagree
    tally["_pairs"] = N * N
    tally["_cpu_seconds"] = round(time.process_time() - t0, 1)
    tally["_width"] = {"W": W, "H": H}
    return tally


def xcheck(kind, k):
    """Every flag of selected rows vs the generic per-pair model (lir_model.Conc)."""
    o = Conc(W)
    rng = random.Random(20261027)
    special = [0, 1, 2, MH, MH + 1, HALF - 1, HALF, HALF + 1, MW - 1, MW]
    rows = sorted(set(special[: max(0, k // 2)] + [rng.randrange(N) for _ in range(k)]))[:k]
    if W == 8:
        rows = list(range(N))
    bad = {}
    for a in rows:
        prod = a * PB32
        if kind == "u":
            _, fast = row_u(a)
            ref_fns = {"u.new": lambda a, b: umulo_new(o, a, b)[1]}
            ref_fns.update({f"u.mut.{m}": (lambda a, b, m=m: umulo_new(o, a, b, m)[1])
                            for m in U_MUTANTS})
        else:
            fast = row_s(a, prod)
            ref_fns = {"s.new": lambda a, b: smulo_new(o, a, b)[1]}
            ref_fns.update({f"s.mut.{m}": (lambda a, b, m=m: smulo_new(o, a, b, m)[1])
                            for m in S_MUTANTS})
        for name, fn in ref_fns.items():
            ref = b8(bytes(1 if fn(a, b) else 0 for b in range(N)))
            if ref != fast[name]:
                bad.setdefault(name, []).append(a)
    return {"rows_checked": len(rows), "rows": rows if W > 8 else "all",
            "fast_vs_generic_disagreements": bad, "width": {"W": W, "H": H}}


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode in ("u", "s"):
        print(json.dumps(run(mode), indent=1))
    else:
        t0 = time.process_time()
        res = xcheck(mode.split("-")[1], int(sys.argv[2]))
        res["_cpu_seconds"] = round(time.process_time() - t0, 1)
        print(json.dumps(res, indent=1))
