from pathlib import Path
import gzip,hashlib,json,re,subprocess
r=Path('/home/ayates/trust-cg-soundness-20260914')
p=Path('/home/ayates/trust-cg-module-receipt-20260920')
qualification=json.loads((r/'cg-module-receipt-qualification-complete.json').read_text())
assert qualification['complete'] and len(qualification['cases'])==12
assert all(row['passed'] for row in qualification['cases'])
records=[r/('cg-module-receipt-'+row['label']) for row in qualification['cases']]
identities=[json.loads((directory/'result.json').read_text()) for directory in records]
assert all(row['passed'] and row['source_unchanged'] for row in identities)
assert len({row['source']['source_fingerprint'] for row in identities})==1
out=p/'reports/perf/2026-09-20-original-module-receipts';out.mkdir()
artifacts=[]
def sha(data):return hashlib.sha256(data).hexdigest()
def put(raw,name):
 compress=name.endswith(('.log','.patch')) or len(raw)>16000
 stored=gzip.compress(raw,mtime=0) if compress else raw
 name+='.gz' if compress else ''
 dest=out/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(stored)
 row=dict(path=name,sha256=sha(raw),bytes=len(raw))
 if compress:row.update(stored_sha256=sha(stored),stored_bytes=len(stored))
 artifacts.append(row)
def copy(src,name):put(src.read_bytes(),name)
def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as stream:
  while chunk:=stream.read(1024*1024):h.update(chunk)
 return h.hexdigest()
for directory in records:
 for path in sorted(directory.rglob('*')):
  if path.is_file():copy(path,'records/'+directory.name+'/'+str(path.relative_to(directory)))
for label in ['source-first','request-first','jit-inputs-first','cache-first','cache-second','cache-diagnostic-first','source-isolated','request-isolated','jit-inputs-isolated','cache-isolated','native-isolated','source-repaired','request-repaired','jit-inputs-repaired','frame-policy-repaired','affine-bytes-repaired','arithmetic-final']:
 directory=r/('cg-module-receipt-'+label)
 for path in sorted(directory.rglob('*')):
  if path.is_file():copy(path,'prior-attempts/'+directory.name+'/'+str(path.relative_to(directory)))
for label in ['module-cache-baseline-first','module-native-baseline-first','module-affine-baseline-first']:
 directory=r/('cg-cell-source-'+label)
 for path in sorted(directory.rglob('*')):
  if path.is_file():copy(path,'prior-attempts/'+directory.name+'/'+str(path.relative_to(directory)))
for name in ['qualify-cg-module-receipts-first-20260920.py','qualify-cg-module-receipts-second-20260920.py','qualify-cg-module-receipts-isolated-20260920.py','qualify-cg-module-receipts-repaired-20260920.py','qualify-cg-module-receipts-final-20260920.py','qualify-cg-module-receipts-tool-bound-20260920.py','run-cg-module-receipt-tool-bound-check-20260920.py','run-cg-module-receipt-check-20260920.py','run-cg-module-receipt-isolated-check-20260920.py','run-cg-cell-check-20260920.py','run-command-to-log.py','archive-cg-module-receipts-20260920.py','cg-module-receipt-qualification-first.log','cg-module-receipt-qualification-second.log','cg-module-receipt-qualification-isolated.log','cg-module-receipt-qualification-repaired.log','cg-module-receipt-qualification-final.log','cg-module-receipt-qualification-tool-bound.log','cg-module-receipt-qualification-complete.json']:
 copy(r/name,'harnesses/'+name)
copy(Path('/home/ayates/ay-pblendvb-repair-20260914/scripts/_oom_guard.py'),'harnesses/_oom_guard.py')
copy(r/'installed-floor-repair-first/identity.json','identities/installed-tools.json')
for name in ['check_linux_aarch64.py','run_with_timeout.py','dependency_identity.py']:
 copy(p/'scripts'/name,'gate-source/'+name)
patch=subprocess.check_output(['git','diff','--binary','HEAD'],cwd=p)
put(patch,'source/tracked.patch')
changed=subprocess.check_output(['git','diff','--name-only','HEAD'],cwd=p,text=True).splitlines()
new=subprocess.check_output(['git','ls-files','--others','--exclude-standard','crates'],cwd=p,text=True).splitlines()
for name in changed+new:
 copy(p/name,'source/files/'+name)
binaries=[]
for directory in records:
 for name in re.findall(r'^\s*Running .+? \(([^\n]+)\)$',(directory/'command.log').read_text(),re.M):
  path=Path(name);path=path if path.is_absolute() else p/path;assert path.is_file()
  binaries.append(dict(campaign=directory.name,path=name,sha256=digest(path),bytes=path.stat().st_size))
assert len(binaries)==11,binaries
tools=[]
for name,value in identities[0]['source']['tools'].items():
 path=Path(value).resolve();tools.append(dict(name=name,path=str(path),sha256=digest(path),bytes=path.stat().st_size))
put((json.dumps(dict(test_binaries=binaries,build_tools=tools),indent=2)+'\n').encode(),'identities/executables.json')
count=sum(int(row['counts'][0][0]) for row in qualification['cases'] if row['counts'])
readme=f'''# Original-module verification receipts and JIT cache binding

Status: PASS for the twelve recorded commands, {count} Rust tests and the verifier-disabled compile check. This is source custody and cache attribution, not a new source-to-machine theorem or complete compiler acceptance.

## Change

AArch64 compiler verification now borrows both the original TrustIR Module and the Module supplied to the LIR adapter. A private, exact lossless binary digest binds both endpoints into captured reports and the JIT verifier-input/cache identity. Source-bearing reports cannot match a legacy LIR-only request. The original/lowered pair survives dialect lowering, per-function proof export and the JIT continuation. This adds no proof credit and does not infer callback memory contracts, dialect correctness or linked-code authority.

Tests retain caller/callee calling-convention, read-only attribute, parameter-type, vararg and target-name mutations on each endpoint with unchanged LIR/machine inputs, plus distinct NaN payload bits. The real cached compiler campaign requires two misses when only the original module changes, two hits on repetition, and two hits when the original source is restored. Existing source and raw-machine negative controls remain required.

The same qualification exposed frame omission for constant-returning scalar leaves. The frame policy now retains the supported source-bound envelope for scalar constants, register copies and conditional returns, as it already does for identity-only and affine arithmetic bodies. Direct frame-policy controls and the existing real encoder/source-frame tests cover this repair.

## Qualification

The final commands use a fresh checkout-specific Cargo target directory, stock Rust 1.97.1, locked/offline dependencies, two build jobs and one test thread. Each command has an exclusive host resource lease, a zero-grace 16 GiB RSS limit and a 1,200-second timeout. All twelve commands pass with unchanged source fingerprints and no selected ignored/skipped tests. The real-tool campaigns use the exact installed AY and Clean identities retained under `identities/`; the package itself is unchanged.

The qualified source is `{identities[0]['source']['source_sha']}` plus the retained tracked patch and two new source files. Its fingerprint is `{identities[0]['source']['source_fingerprint']}`. Complete commands, outputs, resource observations, source/tool identities and resulting test-binary hashes are retained. The immediately preceding clean-main [127-family regression floor](../2026-09-20-linux-complete-callback-floor/README.md) passed 692 tests; that earlier source run is not a whole-floor qualification of this patch.

## Preserved failures

The first coordinator selected the explicitly ignored raw-cache campaign without `--ignored`; it rejected the zero-test result. The corrected invocation then exposed an inherited stale assertion: SXTH's one 16-bit input now receives exhaustive credit within the existing 65,536-tuple budget. The same assertion fails on unchanged main `6e86e6318247f1f84a0c4c3b6baeaad2045a46f1`. The repaired test keeps SXTH as a positive boundary control and uses the real 32-bit NEG input as the statistical, non-reusable receipt control; verification policy is unchanged.

The real high-level native campaign also failed identically on unchanged main: the zero-storage optimization omitted the constant-return leaf frame, invalidating its required formal source-frame coverage. The separate unchanged-main encoder/source-frame suite also fails three tests for constants, parameter copies and conditional diamonds. The first repair handles constants/copies but retains the diamond failure; the final repair covers the conditional return forms too. The fix preserves that evidence-bearing envelope; it does not remove the campaign's formal-frame, stale-source or raw-source controls.

A diagnostic rebuild after switching checkouts reused stale verifier artifacts from the shared Cargo target and failed to find the newly added APIs. The final fresh-directory rebuild eliminates that contamination and reruns every selected case. The first arithmetic integration invocation omitted the managed package prefix from PATH, so Clean discovery could not find the installed checker. It produced provenance failures and was cancelled through the resource guard; the cancelled record is retained. The remaining integration/build commands use the installed package prefix, matching the preceding Linux floor and keeping exact tool identities. The earlier failed commands and logs remain archived under `prior-attempts/`.

## Limits

This record closes neither L01–L14 nor the open source-to-byte calling-frame work. Whole conditional callback models have external independently replayed certificates, but native proof production, justified external premises and production admission remain separate unfinished work. No installed executable was replaced and no statistical evidence was promoted to Formal.
'''
(out/'README.md').write_text(readme)
(out/'inventory.json').write_text(json.dumps(dict(artifacts=artifacts),indent=2)+'\n')
subprocess.run(['python3','scripts/check_evidence_archive.py',str(out)],cwd=p,check=True)
print(json.dumps(dict(report=str(out),artifacts=len(artifacts),tests=count,binaries=len(binaries))),flush=True)
