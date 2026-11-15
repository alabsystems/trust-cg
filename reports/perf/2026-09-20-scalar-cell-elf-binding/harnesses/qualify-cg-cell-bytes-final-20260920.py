from pathlib import Path
import subprocess
r=Path('/home/ayates/trust-cg-soundness-20260914')
commands=[
 ['bytes-final-integration','cargo','test','--locked','--offline','-p','trust-cg-verify','--test','aarch64_scalar_cell_bytes','--test','bridge_copy_types','--test','bridge_signature_layouts','--','--nocapture','--test-threads=1'],
 ['bytes-final-frame','cargo','test','--locked','--offline','-p','trust-cg-verify','--lib','source_bound_frame','--','--nocapture','--test-threads=1'],
]
for command in commands:
 subprocess.run(['python3',str(r/'run-cg-cell-check-20260920.py'),*command],cwd=r,check=True)
