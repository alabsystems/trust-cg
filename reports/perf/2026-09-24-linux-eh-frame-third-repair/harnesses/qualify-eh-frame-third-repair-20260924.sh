#!/bin/bash
# Qualify the third repair of the .eh_frame refusals on clean source:
# tests, source mutants, host survey (wrapped and hidden FDEs).
set -u
R=${RUN_DIR:?output directory}
W=${WORKTREE:?clean checkout of the qualified source}
S=${INPUTS:?directory with survey_list.txt and ehalias_survey_test3.rs}
PKG=${PKG:?AY/Clean package prefix}
export PATH="$PKG/bin:$HOME/.cargo/bin:$PATH" CARGO_TARGET_DIR=${CARGO_TARGET_DIR:?target directory outside the checkout} CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0
rm -rf $R; mkdir -p $R/tests $R/mutation $R/survey
cd $W
{ git rev-parse HEAD; git status --short; } > $R/source.txt
status() { echo "$1" >> $R/status.txt; }
cargo test --locked --offline -j 16 -p trust-cg-codegen --lib > $R/tests/codegen-lib.log 2>&1; status "codegen-lib=$?"
export TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1
cargo test --locked --offline -j 16 -p trust-cg-cli --bins --test link_options --test output_paths -- --nocapture > $R/tests/cli.log 2>&1; status "cli=$?"
for t in e2e_aarch64_link_runtime e2e_aarch64_elf_tlsie e2e_aarch64_eh_linux e2e_aarch64_eh_catch aarch64_elf_cfi_differential e2e_aarch64_elf_link; do
  cargo test --locked --offline -j 16 -p trust-cg-codegen --test $t -- --nocapture > $R/tests/$t.log 2>&1; status "$t=$?"
done
unset TCG_REQUIRE_LLD TCG_REQUIRE_GOLD
mutant() { # name file old new tests...
  local name=$1 file=$2 old=$3 new=$4; shift 4
  python3 - "$file" "$old" "$new" <<'PY'
import sys
p,old,new=sys.argv[1:4]
s=open(p).read()
assert s.count(old)==1,(p,old)
open(p,'w').write(s.replace(old,new))
PY
  git diff > $R/mutation/$name.patch
  for t in "$@"; do eval "$t" >> $R/mutation/$name.log 2>&1; echo "[$t] exit=$?" >> $R/mutation/$name.log; done
  git checkout -- "$file"
  grep -E '^\[' $R/mutation/$name.log | sed "s/^/$name /" >> $R/mutation/summary.txt
}
LIB='cargo test --locked --offline -j 16 -p trust-cg-codegen --lib -- link_driver::'
CLIT='TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1 cargo test --locked --offline -j 16 -p trust-cg-cli --test link_options -- eh_frame_layouts a_table_that_drops'
mutant foreign-record-is-an-error crates/trust-cg-codegen/src/link_driver.rs \
  '                    if length == u32::MAX || past {' \
  '                    if length == u32::MAX || past {
                        if std::hint::black_box(true) {
                            return Err(format!("the .eh_frame record at {at:#x} is not one"));
                        }' "$LIB" "$CLIT"
mutant no-foreign-fde-stop crates/trust-cg-codegen/src/link_driver.rs \
  '                    if id != 0 && !cies.contains_key(&(at + 4).wrapping_sub(u64::from(id))) {' \
  '                    if id != 0 && !cies.contains_key(&(at + 4).wrapping_sub(u64::from(id))) && std::hint::black_box(false) {' "$LIB"
mutant no-entry-past-the-walk crates/trust-cg-codegen/src/link_driver.rs \
  '                        if !terminated && *fde >= at {' \
  '                        if !terminated && *fde >= at && std::hint::black_box(false) {' "$LIB"
mutant static-hidden-observed crates/trust-cg-codegen/src/link_driver.rs \
  '    if let Some((described, found)) = check.overlapping.hidden.first()
        && check.static_executable' \
  '    if let Some((described, found)) = check.overlapping.hidden.first()
        && check.static_executable
        && std::hint::black_box(false)' "$LIB" "$CLIT"
mutant placeholder-hdr-read crates/trust-cg-codegen/src/link_driver.rs \
  '            && (hdr_segment.is_some()' \
  '            && (hdr_segment.is_some() || std::hint::black_box(true)' "$LIB" "$CLIT"
mutant static-ignores-the-table crates/trust-cg-codegen/src/link_driver.rs \
  '        hdr.as_ref()
            .and_then(|hdr| hdr.table.as_ref())' \
  '        hdr.as_ref()
            .filter(|_| !walk.check.static_executable)
            .and_then(|hdr| hdr.table.as_ref())' "$LIB" "$CLIT"
# Host survey (temporary ignored unit test, not committed).
cp $S/ehalias_survey_test3.rs $R/survey/survey_test.rs
WORKTREE=$W INPUTS=$S python3 - <<'PY'
import os
p=os.environ['WORKTREE']+'/crates/trust-cg-codegen/src/link_driver.rs'
s=open(p).read()
anchor='    /// The other address a narrow field\'s bits give: the lowest one, above'
t=open(os.environ['INPUTS']+'/ehalias_survey_test3.rs').read()
assert s.count(anchor)==1
open(p,'w').write(s.replace(anchor,t+anchor))
PY
cp $S/survey_list.txt $R/survey/images.txt
TCG_EH_SURVEY_LIST=$R/survey/images.txt TCG_EH_SURVEY_OUT=$R/survey/verdicts.tsv cargo test --locked --offline -j 16 -p trust-cg-codegen --lib -- tmp_survey_wrap --ignored > $R/survey/survey.log 2>&1; status "survey=$?"
git checkout -- crates/trust-cg-codegen/src/link_driver.rs
awk -F'\t' '{split($2,a,"="); f+=a[2]; w+=($3!="wrapped=0"); o+=($5!="overlapping=0"); v[$4]++} END {print "images", NR; print "fdes", f; print "images_with_wrapped_pointers", w; print "images_with_hidden_fdes", o; for (k in v) print "verdict[" (k==""?"pass":k) "]", v[k]}' $R/survey/verdicts.tsv | sort > $R/survey/summary.txt
awk -F'\t' '$5!="overlapping=0" {print $1"\t"$5"\t"$6}' $R/survey/verdicts.tsv > $R/survey/hidden_fdes.tsv
{ git rev-parse HEAD; git status --short; } > $R/source-final.txt
status DONE
