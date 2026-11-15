"""Exhaustive sweep of the 8-bit analog (4-bit limbs): every (a, b) pair, 65,536 pairs.

Runs the generic LIR model (lir_model.Conc) per pair: the proposed u/s expansions, the
CURRENT division-based expansions, and every mutant. Each flag is compared with the spec
computed from the true (unbounded) product; each value result with a*b mod 2^W.
"""
import json
import sys
import time

from lir_model import (Conc, S_MUTANTS, U_MUTANTS, smulo_div, smulo_new, umulo_div,
                       umulo_new)


def sweep(W):
    o = Conc(W)
    n = 1 << W
    rows = {}

    def run(name, fn, spec):
        bad = 0
        first = None
        for a in range(n):
            for b in range(n):
                r, f = fn(o, a, b)
                if r != (a * b) & o.MW:
                    raise SystemExit(f"{name}: value mismatch at {a},{b}")
                if bool(f) != spec(a, b):
                    bad += 1
                    if first is None:
                        first = (a, b, bool(f), spec(a, b))
        rows[name] = {"mismatches": bad, "first": first}

    run("u.new", umulo_new, o.spec_u)
    run("u.current_div", umulo_div, o.spec_u)
    run("s.new", smulo_new, o.spec_s)
    run("s.current_div", smulo_div, o.spec_s)
    for m in U_MUTANTS:
        run(f"u.mut.{m}", lambda o_, a, b, m=m: umulo_new(o_, a, b, m), o.spec_u)
    for m in S_MUTANTS:
        run(f"s.mut.{m}", lambda o_, a, b, m=m: smulo_new(o_, a, b, m), o.spec_s)
    # dispatch swap: the unsigned expansion on a signed type, and vice versa
    run("s.mut.dispatch_swap(u-expansion)", umulo_new, o.spec_s)
    run("u.mut.dispatch_swap(s-expansion)", smulo_new, o.spec_u)
    # spec sanity: how many pairs overflow at all
    rows["_overflowing_pairs"] = {
        "unsigned": sum(o.spec_u(a, b) for a in range(n) for b in range(n)),
        "signed": sum(o.spec_s(a, b) for a in range(n) for b in range(n)),
        "total": n * n,
    }
    return rows


if __name__ == "__main__":
    W = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    t0 = time.process_time()
    rows = sweep(W)
    rows["_cpu_seconds"] = round(time.process_time() - t0, 1)
    rows["_width"] = {"W": W, "H": W // 2}
    print(json.dumps(rows, indent=1))
