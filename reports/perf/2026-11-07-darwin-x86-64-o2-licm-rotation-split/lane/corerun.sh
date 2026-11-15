#!/bin/zsh
# Re-run the census-o2k-m301-lr compile of core exactly as census_t011_dylib.sh /
# trust_ir_cg_census.py ran it (same trustc, same bridge bytes o2-m301.dylib = o2k-m301-lr.dylib,
# same flags and knobs), plus trace-peephole-entry (no codegen effect), with
#  - stderr filtered to keep only slice_error_fail_rt's peephole-entry dumps (filter.py),
#  - every version of every dumped query snapshotted as it appears (snap.py), so the first
#    codegen attempt's parts survive the second attempt's overwrite.
# Outputs: ~/tcg-scratch/sefrt-diag/corerun/{stderr.log,snap/,snap.log,dump/,obj/}.
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
R=${0:A:h}
rm -rf $R/dump $R/snap $R/obj $R/.stop; mkdir -p $R/dump $R/snap $R/obj
python3 -I $R/snap.py $R/dump $R/snap $R/.stop > $R/snap.log 2>&1 &
SNAP=$!
while [ -e ~/tcg-scratch/quiet.request ]; do sleep 30; done  # as census_t011_dylib.sh
echo "core run start $(date +%H:%M:%S)"
for v in ${(k)parameters[(I)TCG_*]} ${(k)parameters[(I)TRUST_CG_*]}; do unset $v; done  # as trust_ir_cg_census.py:303
RUSTC_BOOTSTRAP=1 $OV/bin/trustc --edition 2024 --crate-type lib --crate-name core --emit=obj \
  -Zcodegen-backend=$HOME/tcg-scratch/runs/o2-m301.dylib -Ccodegen-units=1 -Cpanic=abort -Copt-level=2 -Ztrust-verify=off \
  --out-dir $R/obj -Ztrust-ir-cg-args=diag-json -Ztrust-verify=off -Ztrust-ir-cg-args=x86-body-trace \
  -Ztrust-ir-cg-args=x86-body-dump=$R/dump -Ztrust-ir-cg-args=no-x86-licm -Ztrust-ir-cg-args=no-x86-loop-rotate \
  -Ztrust-ir-cg-args=trace-peephole-entry $HOME/trust/library/core/src/lib.rs 2>&1 | python3 -I $R/filter.py slice_error_fail_rt > $R/stderr.log
echo "core run trustc rc=${pipestatus[1]} $(date +%H:%M:%S)"
touch $R/.stop; wait $SNAP
grep -n 'slice_error_fail_rt' $R/stderr.log | grep TCG-X86-BODY-TRACE | cut -c1-200
cat $R/snap.log | grep slice_error_fail_rt
echo CORERUN-DONE
