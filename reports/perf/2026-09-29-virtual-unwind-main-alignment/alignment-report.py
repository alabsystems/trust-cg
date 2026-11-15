from pathlib import Path
import json,hashlib,gzip,re
p=Path('$HOME/trust-cg/target/virtual-unwind-investigation');out=p.parents[1]/'reports/perf/2026-09-29-virtual-unwind-main-alignment';out.mkdir(exist_ok=True)
def copy(src,name=None):
 src=Path(src);name=name or src.name;data=src.read_bytes()
 if src.suffix in ['.log','.patch'] or src.name.endswith('-lib.rs'):name+='.gz';data=gzip.compress(data,mtime=0)
 (out/name).write_bytes(data)
assert 'test result: ok. 3 passed' in (p/'native-virtual-merged-2.log').read_text()
assert 'test result: ok. 236 passed' in (p/'opt-merged-2.log').read_text()
for f in ['build-merged-2.py','build-merged-2.log','build-merged-2-receipt.json','merged-2-source-head.txt','merged-2-source.patch','merged-2-source-manifest.json','merged-2-lib.rs','qualify-merged-2.py','qualify-merged-2-run.log','opt-build-merged-2.log','opt-build-merged-2-receipt.json','opt-merged-2.log','opt-merged-2-results.json','runtime-merged-2.py','native-virtual-merged-2.log','proof-merged-2.py','proof-merged-2-source.rs','proof-merged-2-results.json','docs-merged-2.py','docs-merged-2-run.log','docs-check-merged-2.log','diagnostics-check-merged-2.log','alignment-report.py']:
 copy(p/f)
rows=json.loads((p/'proof-merged-2-results.json').read_text());summ=[]
for r in rows:
 mode,opt=r['mode'],r['opt'];f=p/f'proof-merged-2-{mode}-O{opt}/compile.log';s=f.read_text();traces=re.findall(r': (\d+) refined, (\d+) skipped .*?, (\d+) memo-hit',s);vals=[sum(int(t[i]) for t in traces) for i in range(3)];u=sum(map(int,re.findall(r'; (\d+) unmodeled shape',s)))
 assert r['returncode']==(0 if mode=='strict' else 1)
 assert (len(traces),*vals,u)==((18,16,0,1,0) if opt==0 else (15,13,0,1,0))
 if mode=='machine':assert 'TCG-PROOF-465' in s
 copy(f,f'proof-merged-2-{mode}-O{opt}.log');summ.append(dict(mode=mode,opt=opt,functions=len(traces),refined=vals[0],skipped=vals[1],memo_hits=vals[2],unmodeled=u))
(out/'proof-summary.json').write_text(json.dumps(summ,indent=2)+'\n')
(out/'README.md').write_text('''# Virtual-unwind main alignment after the x86 increment optimization

Remote main advanced to `f658c8a53` before the [virtual-unwind repair](../2026-09-29-virtual-unwind-filters/README.md) could be pushed. Merge `5e9bf7bbbc9de1015a91a346d1709df216c1ad87` preserves both histories. The incoming production change is an x86 peephole optimization and its tracked option wiring; it makes no speedup claim.

The frozen merged backend is SHA-256 `e02b0a80939f61beb2f3d065b462e5d6704fd9fc3f4b4a98677978e7cc932e5e`. All **236 x86 peephole tests** pass. The Linux AArch64 virtual-call matrix repeats across O0–O3 and both panic policies: 49,152 checks, 7,168 caught panics, 16 reason-checked SIGABRTs, eight forced-unwind executions, and four expected compile refusals with four LLVM controls. The existing frozen native harness and fixtures are identified in the preceding report.

Strict bridge checks retain 18/15 functions, 16/13 refinements, one memo hit each and zero skipped/unmodeled shapes at O0/O2. Machine-proof-required checks remain refused by `TCG-PROOF-465`. Documentation and diagnostic checks pass. The source identity, exact commands, executable/backend hashes and logs are attached and enumerated in `assets.json`.

The previous mixed-library and 223-root O2 std census evidence remains tied to its recorded premerge backend. This alignment does not claim a new std census, whole-CG std, self-hosting, complete machine proof, or performance superiority.
''')
assets={f.name:dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size) for f in sorted(out.iterdir()) if f.name!='assets.json'}
(out/'assets.json').write_text(json.dumps(assets,indent=2)+'\n');print(len(assets),'assets')
