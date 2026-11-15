from pathlib import Path
import hashlib,json,subprocess
r=Path('/home/ayates/trust-cg-soundness-20260914');c=Path('/home/ayates/trust-cg-output-source-capture-20260917');out=r/'cg-const-references-capture-third'
assert json.loads((out/'results.json').read_text())['complete']
expected=json.loads((r/'cg-const-references-capture-third-source.json').read_text())
for name,digest in expected.items():assert hashlib.sha256((c/name).read_bytes()).hexdigest()==digest
# Restore only the exact owned and fingerprinted capture edits.
subprocess.run(['git','restore','--source=HEAD','--staged','--worktree','--',*expected],cwd=c,check=True)
status=subprocess.check_output(['git','status','--porcelain'],cwd=c,text=True);assert not status,status
(out/'capture-restored.json').write_text(json.dumps(dict(clean=True,head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=c,text=True).strip(),restored=list(expected)),indent=2)+'\n')
