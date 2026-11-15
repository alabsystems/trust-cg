#!/usr/bin/env python3
"""z3-check every counterexample a qualification log reports against the matrix's
wrong-lowering query of the same family and label (check_cex.py, for all of them).

usage: check_all_cex.py LOG MATRIX_DIR OUT.tsv
"""
import ast
import json
import re
import subprocess
import sys

Z3 = "$HOME/tcg-scratch/z3-5.1.0/z3-5.1.0-x64-osx-13.3/bin/z3"
FAMILY = {"X86_BODY_QUALIFICATION": "body", "X86_BODY_MEMORY_QUALIFICATION": "memory",
          **{f"X86_BODY_SLICE{n}_QUALIFICATION": f"slice{n}" for n in range(5, 12)}}
log, matrix, out = sys.argv[1:4]
manifest = json.load(open(f"{matrix}/manifest.json"))
queries = {(q["family"], q["label"]): q["file"] for q in manifest["queries"] if q["class"] == "wrong-lowering"}
pattern = re.compile(r"^(X86_BODY_[A-Z0-9_]*QUALIFICATION) refutation=(.*?) result=CounterExample\((\[.*\])\)\s*$")
rows, counts = [], {}
for line in open(log, errors="replace"):
    m = pattern.match(line.rstrip("\n"))
    if not m:
        continue
    family, label, model = FAMILY[m.group(1)], m.group(2), ast.literal_eval(m.group(3))
    file = queries.get((family, label))
    if file is None:
        rows.append((family, label, "no-matrix-query"))
        continue
    text = open(f"{matrix}/{file}").read()
    widths = dict(re.findall(r"\(declare-const (\S+) \(_ BitVec (\d+)\)\)", text))
    if any(name not in widths for name, _ in model):
        rows.append((family, label, "model-names-differ"))
        continue
    pins = "".join(f"(assert (= {n} (_ bv{v} {widths[n]})))\n" for n, v in model)
    text = re.sub(r"\(set-option :timeout \d+\)\n", "", text).replace("(check-sat)", pins + "(check-sat)")
    verdict = subprocess.run([Z3, "-in", "-T:60"], input=text, capture_output=True, text=True).stdout.split()
    rows.append((family, label, verdict[0] if verdict else "?"))
with open(out, "w") as o:
    for row in rows:
        o.write("\t".join(row) + "\n")
        counts[row[2]] = counts.get(row[2], 0) + 1
print(counts)
