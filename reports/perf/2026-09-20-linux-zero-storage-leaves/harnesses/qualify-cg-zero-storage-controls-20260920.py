from pathlib import Path
import hashlib,json,os,signal,subprocess,sys,time
r=Path('/home/ayates/trust-cg-soundness-20260914');out=r/'cg-zero-storage-controls-second';out.mkdir()
native=r/'cg-zero-storage-native-first';report=json.loads((native/'results.json').read_text());assert report['complete'] and report['execution_cases']==19
sys.path.insert(0,'/home/ayates/ay-pblendvb-repair-20260914/scripts');import _oom_guard as guard
plan=guard.plan_solver_resources(jobs=1,mem_floor_mb=16384,label='Frameless native unwind and oracle mutation controls')
records=[]
for case in report['cases']:
 if 'execution' not in case:continue
 frames=(native/case['name']/'unwind.log').read_text()
 assert 'Return address column: 30' in frames and 'DW_CFA_def_cfa: r31 (sp) ofs 0' in frames
 assert frames.count(' FDE ')==1
 assert all(line.strip().startswith(('DW_CFA_nop','DW_CFA_def_cfa: r31 (sp) ofs 0')) for line in frames.splitlines() if 'DW_CFA_' in line)
 records.append(dict(case=case['name'],unwind_sha256=hashlib.sha256(frames.encode()).hexdigest(),passed=True))
writer=native/'output_memory_writer-O1';base='    str x1, [x0]\n    str x2, [x0,#8]\n    str x3, [x0,#16]\n    str x4, [x0,#24]\n    str x5, [x0,#32]\n'
mutants=[('correct','',0),('wrong-word','    str xzr, [x0,#32]\n',1),('before-buffer','    str xzr, [x0,#-8]\n',1),('after-buffer','    str xzr, [x0,#40]\n',1),('saved-gpr','    mov x19, #99\n',77),('saved-fpr','    fmov d8, xzr\n',77),('frame-pointer','    sub x29, x29, #16\n',77),('stack-pointer','    sub sp, sp, #16\n',77)]
for name,mutation,expected in mutants:
 asm=out/(name+'.S');asm.write_text('.text\n.global output_memory_writer\n.type output_memory_writer,%function\noutput_memory_writer:\n'+base+mutation+'    ret\n.section .note.GNU-stack,"",%progbits\n')
 exe=out/name
 commands=[['cc','-std=c11','-Wall','-Wextra','-Werror',str(writer/'runner.c'),str(writer/'abi.S'),str(asm),'-o',str(exe)],[str(exe)]]
 case=dict(name=name,expected_exit=expected,runs=[])
 for idx,command in enumerate(commands):
  result=guard.run_captured(command,16384,60,label=name)
  (out/(name+f'-{idx}.log')).write_text(result.stdout+result.stderr)
  assert not (result.memout or result.timed_out or result.cancelled or result.stdout_truncated or result.stderr_truncated)
  assert result.returncode==(0 if idx==0 else expected),(name,idx,result.returncode)
  case['runs'].append(dict(command=command,exit_code=result.returncode,seconds=result.wall_sec,guard_evidence=result.guard_evidence))
 records.append(case)
(out/'results.json').write_text(json.dumps(dict(passed=True,resources=plan._asdict(),rss_limit_mb=16384,grace_mb=0,scope='Nineteen independently decoded native CFI records; positive writer oracle plus seven deliberate output/bounds/ABI mutations rejected. Mutation bodies are test controls, not compiler output.',records=records),indent=2)+'\n')
print('19 CFI records PASS; positive oracle PASS; 7 bad-output/ABI controls rejected')
