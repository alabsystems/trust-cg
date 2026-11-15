from pathlib import Path
import json,gzip,hashlib
p=Path('$HOME/trust-cg/target/zst-tuple-investigation')
b=p.parent/'array-union-transmute-investigation'
out=p.parents[1]/'reports/perf/2026-09-29-zero-sized-tuples-std-census'
out.mkdir(exist_ok=True)
delta=json.loads((p/'std-delta-first.json').read_text()); assert delta['counts']==[233,231] and not delta['added'] and not delta['changed']
def copy(src,name=None):
 name=name or src.name;data=src.read_bytes()
 if src.suffix in ['log','patch']:data=gzip.compress(data,mtime=0);name+='.gz'
 (out/name).write_bytes(data)
for name in ['std-delta-first.json','std-delta.py','isolate.py','std-O2-first-results.json','first-source-head.txt','first-source-manifest.json','first-source.patch','build-first-receipt.json']:
 copy(p/name)
copy(b/'std-O2-first-results.json','before-results.json')
copy(b/'first-source-manifest.json','before-source-manifest.json')
copy(p/'std-O2-first/compile.log','after-compile.log')
copy(b/'std-O2-first/compile.log','before-compile.log')
copy(p/'census-supplement.py')
(out/'README.md').write_text('''# Zero-sized tuple optimized standard-library census

The completed Linux AArch64 O2 diagnostic `std` census decreased from **233 to 231 failing roots**: two removed, zero added, zero changed. The removed failures are `ControlFlow::map_break` and its `FnOnce` constructor shim over `((),)`. Both runs completed with exit 1; neither timed out. This is still an incomplete `std` build using the recorded LLVM dependency artifacts.

This supplements the [published tuple report](../2026-09-29-zero-sized-tuples/README.md), whose census was still running when it was published. Its earlier evidence is unchanged.

The baseline backend is `e7c28938cf451256377e7a1b23d91be4f58ddd94222585619199345672b4a3b8`; the tuple backend is `1a6cc67befb08366c2523a3c09e71cd4ea73564fbe71ac10ca6432dc055f8e13`. The tuple backend predates the later sealed JIT merge. Both use Trust IR `824174a164de10dba2053e387dfc4b1140960885` and the same recorded LLVM dependency cohort; the intervening main merge also includes x86 jump-table changes. Source manifests, exact commands, complete diagnostics and the root delta are attached and hashed in `assets.json`.

The separate latest O0 census remains 197 failures. Whole-CG standard-library completion, self-hosting, complete machine proof, and strict compile-time/runtime superiority over LLVM and Clang remain open.
''')
for f in [p/'std-O2-first-results.json',b/'std-O2-first-results.json']:
 x=json.loads(f.read_text());assert x['returncode']==1 and not x['timed_out']
assets={f.name:{'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size} for f in sorted(out.iterdir()) if f.name!='assets.json'}
(out/'assets.json').write_text(json.dumps(assets,indent=2)+'\n')
print(out,len(assets))
