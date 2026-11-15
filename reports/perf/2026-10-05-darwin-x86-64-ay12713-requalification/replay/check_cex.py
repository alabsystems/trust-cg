#!/usr/bin/env python3
"""Check an AY counterexample with z3: pin every named variable of the model in the
wrong-lowering query and ask z3 for satisfiability (sat = a genuine counterexample).

usage: check_cex.py QUERY.smt2 'CounterExample([("x", 1), ...])'
"""
import ast
import re
import subprocess
import sys

Z3 = "$HOME/tcg-scratch/z3-5.1.0/z3-5.1.0-x64-osx-13.3/bin/z3"
query, model = sys.argv[1], sys.argv[2]
pairs = ast.literal_eval(re.search(r"CounterExample\((\[.*\])\)", model).group(1))
text = open(query).read()
widths = dict(re.findall(r"\(declare-const (\S+) \(_ BitVec (\d+)\)\)", text))
pins = "".join(f"(assert (= {name} (_ bv{value} {widths[name]})))\n" for name, value in pairs)
text = re.sub(r"\(set-option :timeout \d+\)\n", "", text)
text = text.replace("(check-sat)", pins + "(check-sat)")
out = subprocess.run([Z3, "-in", "-T:60"], input=text, capture_output=True, text=True).stdout.strip()
print(f"{query.split('/')[-1]}\tpinned={len(pairs)}\tz3={out.splitlines()[0] if out else '?'}")
