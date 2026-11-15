"""Exhaustive 16-bit / 8-bit-limb sweep of the proposed expansions: all 2^32 (a, b) pairs.

Lean evaluator: one Python int per quantity, 32-bit lanes over all 65,536 values of b, no
int<->bytes conversions in the row loop. Limb products with a scalar limb come from
precomputed lane tables (x * b0 and x * b1 for every x).

Spec (threshold spelling, all rows): unsigned a*b >= 2^16 <=> b > (2^16-1)//a; signed via
the exact interval of b with a*b in [-2^15, 2^15).

Cross-checks on every STRIDE-th row and on special rows (sweep_fast, which equals the
generic per-op model on every pair at W = 8 and on sampled rows at W = 16):
  * lean flag == sweep_fast flag, lane by lane;
  * product-spelled spec (sweep_fast.spec_u/spec_s) == threshold spec;
  * mutant mismatch counts on those rows.

usage: sweep16.py u|s [a_lo a_hi] [stride]
"""
import json
import sys
import time

sys.argv, _argv = ["sweep_fast", "u", "16"], sys.argv
import sweep_fast as sf  # noqa: E402

sys.argv = _argv

W, H, N = 16, 8, 1 << 16
MW, MH, HALF = 0xFFFF, 0xFF, 0x8000
REP32 = sf.REP32
MW32, MH32 = MW * REP32, MH * REP32
G32 = 0x100 * REP32
PB32 = sf.PB32
LANE = 32


def lanes(values):
    return int.from_bytes(sf.array("I", values).tobytes(), "little")


def lane_tables(y0_vals, y1_vals, y1nz):
    """lo/hnz lane tables of x*y0 and x*y1 for every 8-bit x; O1 table folds in `both`."""
    P0, P1 = lanes(y0_vals), lanes(y1_vals)
    lo0, o1b, lo1, hnz1 = [], [], [], []
    for x in range(256):
        q0, q1 = x * P0, x * P1
        lo0.append(q0 & MH32)
        h0 = (((q0 >> 8) + MH32) >> 8) & REP32
        o1b.append(h0 | (y1nz if x else 0))
        lo1.append(q1 & MH32)
        hnz1.append((((q1 >> 8) + MH32) >> 8) & REP32)
    return lo0, o1b, lo1, hnz1


def popcount_range(F, lo, hi):
    """number of set lanes in [lo, hi] (each lane holds 0/1 in bit 0)."""
    if hi < lo:
        return 0
    return (F >> (LANE * lo)).bit_count() - (F >> (LANE * (hi + 1))).bit_count()


def u_spec_range(a):
    if a == 0:
        return None
    k = MW // a
    return (k + 1, N - 1) if k + 1 <= N - 1 else None


def s_spec_range(a):
    s = sf.sx(a, W)
    if s == 0:
        return None
    lo_v, hi_v = -HALF, HALF - 1
    if s > 0:
        blo, bhi = -((-lo_v) // s), hi_v // s
    else:
        blo, bhi = -((-hi_v) // s), lo_v // s
    blo, bhi = max(blo, -HALF), min(bhi, HALF - 1)
    # pattern order: 0..HALF-1 are 0..HALF-1, HALF..N-1 are -HALF..-1; 0 never overflows,
    # so the overflowing patterns are one contiguous run.
    lo_p, hi_p = bhi + 1, (N + blo - 1) if blo < 0 else N - 1
    return (lo_p, hi_p) if lo_p <= hi_p else None


def mismatches(F, rng):
    total = F.bit_count()
    if rng is None:
        return total
    inside = popcount_range(F, *rng)
    return (total - inside) + ((rng[1] - rng[0] + 1) - inside)


def spec_bits(rng):
    if rng is None:
        return 0
    lo, hi = rng
    return sum(1 << (8 * i) for i in ()) if False else int.from_bytes(
        bytes(lo) + b"\x01" * (hi - lo + 1) + bytes(N - 1 - hi), "little")


def to_b8(F):
    return sf.b8(sf.l32_byte0(F))


def main():
    mode = sys.argv[1]
    a_lo = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    a_hi = int(sys.argv[3]) if len(sys.argv) > 3 else N
    stride = int(sys.argv[4]) if len(sys.argv) > 4 else 64
    t0 = time.process_time()
    if mode == "u":
        LO0, O1B, LO1, HNZ1 = lane_tables([b & MH for b in range(N)], [b >> 8 for b in range(N)],
                                          lanes([1 if b >> 8 else 0 for b in range(N)]))
    else:
        ub = [abs(sf.sx(b, W)) & MW for b in range(N)]
        LO0, O1B, LO1, HNZ1 = lane_tables([u & MH for u in ub], [u >> 8 for u in ub],
                                          lanes([1 if u >> 8 else 0 for u in ub]))
        SB32 = lanes([b >> 15 for b in range(N)])
        NSB32 = SB32 ^ REP32
        SBM32, NSBM32 = SB32 * MW, NSB32 * MW
    t_tables = time.process_time() - t0

    special = {0, 1, 2, 0xFF, 0x100, 0x101, HALF - 1, HALF, HALF + 1, MW - 1, MW}
    bad_pairs = 0
    first_bad = None
    checked_rows = 0
    xrows = 0
    xdis = {"lean_vs_sweep_fast": 0, "spec_product_vs_threshold": 0}
    mut = {}
    for a in range(a_lo, a_hi):
        P = a * PB32
        if mode == "u":
            a0, a1 = a & MH, a >> 8
            R1G = ((P >> 8) & MH32) | G32
            T = (LO0[a1] + LO1[a0]) & MH32
            GE = ((R1G - T) >> 8) & REP32
            F = O1B[a1] | HNZ1[a0] | (GE ^ REP32)
            rng = u_spec_range(a)
        else:
            sa = a >> 15
            ua = abs(sf.sx(a, W)) & MW
            ua0, ua1 = ua & MH, ua >> 8
            NEG, NEGM = (NSB32, NSBM32) if sa else (SB32, SBM32)
            r = P & MW32
            pu = ((r ^ NEGM) + NEG) & MW32
            PU1G = ((pu >> 8) & MH32) | G32
            T = (LO0[ua1] + LO1[ua0]) & MH32
            GE = ((PU1G - T) >> 8) & REP32
            OU = O1B[ua1] | HNZ1[ua0] | (GE ^ REP32)
            rneg = (r >> 15) & REP32
            rnz = ((r + MW32) >> 16) & REP32
            F = OU | ((rneg ^ NEG) & rnz)
            rng = s_spec_range(a)
        d = mismatches(F, rng)
        checked_rows += 1
        if d:
            bad_pairs += d
            if first_bad is None:
                first_bad = a
        if a % stride == 0 or a in special:
            xrows += 1
            if mode == "u":
                _, out = sf.row_u(a)
                fast_flag, spec_p, name = out["u.new"], sf.spec_u(P), "u"
            else:
                out = sf.row_s(a, P)
                fast_flag, spec_p, name = out["s.new"], sf.spec_s(a), "s"
            if to_b8(F) != fast_flag:
                xdis["lean_vs_sweep_fast"] += 1
            spec_t = spec_bits(rng)
            if spec_p != spec_t:
                xdis["spec_product_vs_threshold"] += 1
            for k, v in out.items():
                e = mut.setdefault(k, {"mismatch_pairs": 0, "rows_with_mismatch": 0})
                dd = (v ^ spec_p).bit_count()
                e["mismatch_pairs"] += dd
                e["rows_with_mismatch"] += 1 if dd else 0
    res = {
        "mode": mode, "width": {"W": W, "H": H}, "a_range": [a_lo, a_hi],
        "pairs_checked": checked_rows * N, "new_expansion_mismatch_pairs": bad_pairs,
        "first_bad_a": first_bad,
        "crosscheck_rows": xrows, "crosscheck_disagreements": xdis,
        "on_crosscheck_rows_vs_product_spec": mut,
        "cpu_seconds": round(time.process_time() - t0, 1),
        "table_cpu_seconds": round(t_tables, 1),
    }
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    main()
