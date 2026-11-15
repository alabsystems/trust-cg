#!/usr/bin/env python3
"""COI-reduce every query of DIR into OUTDIR.  usage: coi_dir.py DIR OUTDIR"""
import os, subprocess, sys
here = os.path.dirname(os.path.abspath(__file__))
d, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
for f in sorted(os.listdir(d)):
    if f.endswith(".smt2"):
        subprocess.run([sys.executable, os.path.join(here, "coi.py"), os.path.join(d, f), os.path.join(out, f)],
                       stdout=subprocess.DEVNULL, check=True)
print("done")
