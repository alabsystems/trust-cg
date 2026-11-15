from pathlib import Path
import dataclasses,hashlib,json,os,re,subprocess,sys
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917');out=r/('cg-floor-repair-tests-'+sys.argv[1]);out.mkdir()
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
resources=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Repair complete Linux floor failures')
env={k:v for k,v in os.environ.items() if not k.startswith(('TCG_','TRUST_CG_','AY_')) and k not in ['RUSTC','RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_TARGET']}
env.update(RUSTUP_TOOLCHAIN='1.97.1',CARGO_BUILD_JOBS='2',RUST_TEST_THREADS='1',RUST_MIN_STACK='16777216',CARGO_TARGET_DIR='$HOME/trust-cg/target',PATH='/home/ayates/.rustup/toolchains/1.97.1-aarch64-unknown-linux-gnu/bin:/home/ayates/.local/lib/trust-cg/47c6c194-ay43f133d3-cleaned2a80d1/bin:/home/ayates/.cargo/bin:/home/ayates/.local/bin:/usr/bin:/bin')
def git(*args):return subprocess.check_output(['git',*args],cwd=p,text=True).strip()
def inventory():
 names=set(git('ls-files').splitlines())|set(git('ls-files','--others','--exclude-standard').splitlines())
 return {n:hashlib.sha256((p/n).read_bytes()).hexdigest() for n in names if n.endswith(('.rs','.toml','Cargo.lock','.sh','.py'))}
head=git('rev-parse','HEAD');before=inventory();rows=[]
(out/'request.json').write_text(json.dumps(dict(head=head,inputs=before,resources=resources._asdict(),environment={k:env[k] for k in ['PATH','RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','RUST_TEST_THREADS','RUST_MIN_STACK','CARGO_TARGET_DIR']},rss_limit_mb=16384,grace_mb=0),indent=2)+'\n')
commands=[]
for package,target,filter_ in [
 ('trust-cg-codegen','e2e_aarch64_fptosi_sat_i128',None),
 ('trust-cg-codegen','e2e_aarch64_i128_to_f16',None),
 ('trust-cg-codegen','e2e_aarch64_f16_to_i128',None),
 ('trust-cg-lower','niche_enum_codec',None),
 ('trust-cg-lower','direct_enum_projection',None),
 ('trust-cg-codegen','e2e_aarch64_niche_enum_linux',None),
 ('trust-cg-codegen','e2e_aarch64_niche_enum','backend_refuses'),
 ('trust-cg-codegen','enum_field_projection',None),
 ('trust-cg-codegen','core_jit_planning',None),
 ('trust-cg-codegen','jit_fail_closed_proof_policy',None),
 ('trust-cg-codegen','jit_source_bound_arithmetic',None),
 ('trust-cg-codegen','e2e_aarch64_link_runtime',None),
 ('trust-cg-codegen','aarch64_live_frame_effects',None),
]:
 command=['cargo','test','--locked','--offline','-p',package,'--test',target,'-j','2',*([filter_] if filter_ else []),'--','--nocapture','--test-threads=1'];commands.append((target,command))
commands.append(('frame',['cargo','test','--locked','--offline','-p','trust-cg-codegen','--lib','frame::','-j','2','--','--test-threads=1']))
commands.append(('adapter',['cargo','test','--locked','--offline','-p','trust-cg-lower','--lib','adapter','-j','2','--','--test-threads=1']))
commands.append(('fmt',['bash','scripts/check_fmt.sh']))
for name,command in commands:
 log=out/(name+'.log');result=guard.run_captured(['python3',str(r/'run-command-to-log.py'),str(log),*command],16384,1800,label=name,env=env,cwd=p)
 capture=dataclasses.asdict(result);(out/(name+'.capture.json')).write_text(json.dumps(capture,indent=2)+'\n')
 row=dict(name=name,command=command,exit_code=result.returncode,seconds=result.wall_sec,guard_evidence=result.guard_evidence,tests=re.findall(r'^test result:.*$',log.read_text(),re.M));rows.append(row)
 (out/'results.json').write_text(json.dumps(dict(head=head,complete=False,results=rows),indent=2)+'\n');print(json.dumps(row),flush=True)
 assert not(result.returncode or result.memout or result.timed_out or result.cancelled or result.stdout_truncated or result.stderr_truncated),name
 assert git('rev-parse','HEAD')==head and inventory()==before
 if name!='fmt':assert len(row['tests'])==1 and re.search(r'test result: ok\. [1-9]\d* passed; 0 failed; 0 ignored;',row['tests'][0]),name
(out/'results.json').write_text(json.dumps(dict(head=head,complete=True,passed=True,inputs_unchanged=inventory()==before,results=rows),indent=2)+'\n')
