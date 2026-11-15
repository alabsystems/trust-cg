#!/bin/zsh
# Everything that runs AY on the final code, strictly one after another (one solver at a time;
# replay19.py and qualify19.sh each wait on quiet.request, a census or any other AY):
# (1) the final bytes of the 41 roots (whole, then claims as the bridge replays them, then the
# certified claims' resident leg) and the seven wide functions; (2) after the final test build,
# every qualification lane, one test per process; (3) the remaining library tests that run
# fixture solvers (ay_bridge, the negative memo, the export); (4) the codegen gate; (5) the
# whole-core regression check, one-shot.
S=$HOME/tcg-scratch/s19; R=$S/replay; W=$HOME/tcg-scratch/wt-s19
until grep -q "CHAIN-FIX-PROBES-DONE" $S/logs/chain_fix.log 2>/dev/null || ! pgrep -f "[c]hain_fix.sh" >/dev/null; do sleep 20; done
grep -q "CHAIN-FIX-PROBES-DONE" $S/logs/chain_fix.log || { echo "chain_fix died before its probes"; exit 1; }
cd $R
echo "== s3c whole $(date +%H:%M)"; python3 measure.py run $S/redump/s3c_mapped s3c
echo "== s3c claims $(date +%H:%M)"; python3 claims_seq.py $S/redump/s3c_mapped $S/redump/s3c_mapped_claims
python3 - <<'PY'
import json, hashlib, os, shutil
S = os.path.expanduser('~/tcg-scratch/s19')
fr = {json.loads(l)['sha'] for l in open(f'{S}/replay/results/fresh.jsonl')}
C, D = f'{S}/redump/s3c_mapped_claims', f'{S}/redump/s3c_claims_replayed'
shutil.rmtree(D, ignore_errors=True); os.makedirs(D)
for c in sorted(os.listdir(C)):
    if hashlib.sha256(open(f'{C}/{c}', 'rb').read()).hexdigest() in fr:
        shutil.copyfile(f'{C}/{c}', f'{D}/{c}')
PY
echo "== s3c claims resident $(date +%H:%M)"; python3 measure.py run $S/redump/s3c_claims_replayed s3c-claims
echo "== wide s3c $(date +%H:%M)"; python3 measure.py run $S/redump/wide_s3c_mapped wide-s3c --fresh-only
python3 measure.py score $S/redump/s3c_mapped --claims $S/redump/s3c_mapped_claims | tail -1
python3 measure.py score $S/redump/s3c_mapped --claims $S/redump/s3c_mapped_claims --retry | tail -1
echo "S3C-DONE $(date)"
until grep -q "CHAIN-FIX-DONE" $S/logs/chain_fix.log 2>/dev/null || ! pgrep -f "[c]hain_fix.sh" >/dev/null; do sleep 30; done
[ -x $S/testbin_final3 ] || { echo "no final3 binary"; exit 1; }
echo "== qualification $(date +%H:%M)"
rm -rf $S/qual/final
$S/qual/qualify19.sh $W $S/testbin_final3 $S/qual/final $(cat $S/qual/listed.txt)
echo "QUAL-DONE $(date)"
echo "== fixture-solver library tests $(date +%H:%M)"
cd $W/crates/trust-cg-verify
RUST_MIN_STACK=67108864 nice -n 19 $S/testbin_final3 ay_bridge:: source_bound_negative_memo:: source_bound_replay:: verdict_db:: function_request:: --test-threads=2 > $S/logs/libtests_final.log 2>&1
grep -E "^test result|FAILED" $S/logs/libtests_final.log | head
echo "== codegen gate $(date +%H:%M)"
cd $W
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556
TRUST_TARGO=$OV/bin/targo CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s19 TCG_X86_BODY_QUALIFY_AY=$OV/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OV/bin/clean nice -n 19 bash scripts/trust_cargo.sh test --no-fail-fast -p trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus -j2 > $S/logs/gate_codegen.log 2>&1
grep -E "^test result|FAILED" $S/logs/gate_codegen.log | head
echo "== regress $(date +%H:%M)"
cd $R
S19_CENSUS_LOG=$HOME/tcg-scratch/runs/census-s20/stderr.log python3 regress.py prepare $S/all/base20 $S/all/s3c $S/regress/s3c
python3 measure.py run $S/regress/s3c/queries s3c-regress --fresh-only > $S/logs/regress_s3c.log 2>&1
python3 regress.py report $S/regress/s3c >> $S/logs/regress_s3c.log 2>&1
tail -20 $S/logs/regress_s3c.log
echo "CHAIN-MEAS5-DONE $(date)"
