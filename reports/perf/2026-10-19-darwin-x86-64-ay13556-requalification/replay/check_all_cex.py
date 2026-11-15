#!/usr/bin/env python3
"""z3-check every wrong lowering's counterexample a qualification ledger reports (every
`refutation=` line and slice 16's refuted parts; slice 1's one UF + world swap is evidence
about an encoding, not a wrong lowering, and is not checked here): pin every variable of AY's
model into the wrong lowering's own query and ask z3 5.1.0 for satisfiability (`sat` = a
genuine counterexample).

usage: check_all_cex.py LEDGER_DIR MATRIX_CAPTURE OUT.tsv

The query is the lane's own dump (`<test>/queries/refutation_<label>.smt2`, slices 11-17,
ArrayGep and the bool sign extension) or, for the lanes that dump none (slices 1, 4-10), the
wrong-lowering query of the same family and label in the qualification matrix's capture
(`print_slice_ten_fixtures` with `TCG_X86_BODY_QUALIFICATION_MATRIX=1`), read from its
`X86_BODY_MATRIX` JSON lines directly: `scripts/export_x86_qualification_matrix.py` refuses
main's capture at its first slice-15 record (a family it does not know). Adapted from the AY
12713 record's `replay/check_all_cex.py`.
"""
import ast
import json
import os
import re
import subprocess
import sys

Z3 = "$HOME/tcg-scratch/z3-5.1.0/z3-5.1.0-x64-osx-13.3/bin/z3"
FAMILY = {"X86_BODY_QUALIFICATION": "body", "X86_BODY_MEMORY_QUALIFICATION": "memory",
          **{f"X86_BODY_SLICE{n}_QUALIFICATION": f"slice{n}" for n in range(5, 18)}}
LINE = re.compile(r"(X86_BODY_[A-Z0-9_]*QUALIFICATION) refutation=(.*?) result=CounterExample\((\[.*?\])\)")
# Slice 16's wrong lowerings are stated in parts, each refuted on its own part's query.
PART = re.compile(r"(X86_BODY_SLICE16_QUALIFICATION) shape=refutation (.*?) part=(\d+) "
                  r"result=CounterExample\((\[.*?\])\)")


def norm(text):
    return re.sub(r"[^a-z0-9]", "", text.lower())


def main():
    ledger, matrix, out = sys.argv[1:4]
    records = [json.loads(line[len("X86_BODY_MATRIX\t"):]) for line in open(matrix)
               if line.startswith("X86_BODY_MATRIX\t")]
    by_label = {(r["family"], r["label"]): r["smt2"] for r in records
                if r.get("kind") == "query" and r.get("class") == "wrong-lowering"}
    rows, counts = [], {}
    for name in sorted(os.listdir(ledger)):
        if not name.endswith(".log"):
            continue
        test = name[:-4]
        qdir = os.path.join(ledger, test, "queries")
        dumped = {}
        if os.path.isdir(qdir):
            for f in os.listdir(qdir):
                if f.startswith("refutation_") and f.endswith(".smt2"):
                    dumped[norm(f[len("refutation_"):-len(".smt2")])] = os.path.join(qdir, f)
        for line in open(os.path.join(ledger, name), errors="replace"):
            m, part = LINE.search(line), PART.search(line)
            if part:
                lane, label, model = part.group(1), f"{part.group(2)}.part{part.group(3)}", \
                    ast.literal_eval(part.group(4))
            elif m:
                lane, label, model = m.group(1), m.group(2), ast.literal_eval(m.group(3))
            else:
                continue
            path = dumped.get(norm(label))
            if path is not None:
                source, text = "lane-dump", open(path).read()
            else:
                source, text = "matrix", by_label.get((FAMILY.get(lane), label))
            if text is None:
                rows.append((test, label, "-", "no-query"))
                continue
            widths = dict(re.findall(r"\(declare-const (\S+) \(_ BitVec (\d+)\)\)", text))
            if any(n not in widths for n, _ in model):
                rows.append((test, label, source, "model-names-differ"))
                continue
            pins = "".join(f"(assert (= {n} (_ bv{v} {widths[n]})))\n" for n, v in model)
            text = re.sub(r"\(set-option :timeout \d+\)\n", "", text).replace("(check-sat)", pins + "(check-sat)", 1)
            verdict = subprocess.run([Z3, "-in", "-T:60"], input=text, capture_output=True,
                                     text=True).stdout.split()
            rows.append((test, label, source, verdict[0] if verdict else "?"))
    with open(out, "w") as o:
        for row in rows:
            o.write("\t".join(row) + "\n")
            counts[row[3]] = counts.get(row[3], 0) + 1
    print(len(rows), counts)


main()
