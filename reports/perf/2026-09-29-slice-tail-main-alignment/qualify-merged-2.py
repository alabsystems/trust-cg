from pathlib import Path
import subprocess, json, shutil, hashlib, time
p = Path('$HOME/trust-cg/target/slice-from-end-investigation')
root = p.parents[1]
def sha(f): return hashlib.sha256(f.read_bytes()).hexdigest()
files = [root/x for x in subprocess.check_output(['git','ls-files'],cwd=root,text=True).splitlines() if (root/x).is_file() and x.endswith(('.rs','.toml','.lock'))]
(p/'root-merged-2-inputs.json').write_text(json.dumps({str(f.relative_to(root)):sha(f) for f in files},indent=2)+'\n')
cmd = ['python3',str(p/'workspace-online.py'),'test']
for pkg in ['opt','verify','codegen','cli','lower','test']: cmd += ['-p','trust-cg-'+pkg]
cmd += ['--lib']
for test in ['must_refuse_corpus','x86_icmp_manifest_cells','trust_ir_construct_inventory','x86_vector_icmp_admission','aarch64_instruction_word_binding','emit_proofs_flag','dependency_authority']: cmd += ['--test',test]
cmd += ['--no-run','--message-format=json']
with (p/'root-build-merged-2.log').open('wb') as f:
    r = subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=1800)
assert r.returncode == 0, r.returncode
events = []
for line in (p/'root-build-merged-2.log').read_text().splitlines():
    try: events.append(json.loads(line))
    except ValueError: pass
assert any(e.get('reason')=='build-finished' and e['success'] for e in events)
artifacts = {}; receipts = []
for e in events:
    if e.get('reason')!='compiler-artifact' or not e.get('executable'): continue
    pkg = e['package_id'].split('/')[-1].split('#')[0]
    name = e['target']['name']; key = (pkg, name)
    assert key not in artifacts, key
    src=Path(e['executable']); dst=p/f'{pkg}-{name}-merged-2.test'
    shutil.copy2(src,dst); artifacts[key]=dst
    receipts.append(dict(command=cmd,package=pkg,target=name,original_path=str(src),immutable_path=str(dst),sha256=sha(dst)))
(p/'root-build-merged-2-receipt.json').write_text(json.dumps(receipts,indent=2)+'\n')
print('root built',flush=True)
exec((p/'env.py').read_text())
env['XDG_CACHE_HOME']='/tmp/trust-cg-borrowed-aggregate-proof-qjyzzw76'
groups = []
for name,filter in [('flags','tcg_env_flag_tests::'),('peephole','x86_peephole::tests::'),('licm','x86_licm::tests::'),('effects','effects::tests'),('cse','x86_cse::tests::')]:
    groups.append((name,'trust-cg-opt','trust_cg_opt',filter))
groups += [
    ('diag','trust-cg-verify','trust_cg_verify','diag::tests::'),
    ('ub-map','trust-cg-verify','trust_cg_verify','fsym_ub_map'),
    ('icmp-cells','trust-cg-verify','x86_icmp_manifest_cells',''),
    ('constructs','trust-cg-lower','trust_ir_construct_inventory',''),
    ('vector-admission','trust-cg-lower','x86_vector_icmp_admission',''),
    ('binding','trust-cg-codegen','aarch64_instruction_word_binding',''),
    ('codegen-corpus','trust-cg-codegen','must_refuse_corpus',''),
    ('cli-corpus','trust-cg-cli','must_refuse_corpus',''),
    ('cli-proof','trust-cg-cli','emit_proofs_flag',''),
    ('authority','trust-cg-test','dependency_authority',''),
]
rows=[]
for label,pkg,name,filter in groups:
    dst=artifacts[(pkg,name)]; cmd=[str(dst),filter,'--nocapture','--test-threads=1']
    log=p/f'root-{label}-merged-2.log'; start=time.monotonic()
    with log.open('wb') as f: r=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=900)
    rows.append(dict(command=cmd,log=str(log),returncode=r.returncode,wall_seconds=time.monotonic()-start,sha256=sha(dst)))
    (p/'root-merged-2-results.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(label,r.returncode,flush=True)
    if r.returncode: raise SystemExit(r.returncode)
for row in receipts:
    if row['target']=='trust-cg': assert sha(Path(row['original_path']))==row['sha256']
