#!/bin/bash
# Qualify the hostile-product repair of the linked-image checks on clean
# source: tests, source mutants, host .eh_frame survey, hostile-image A/B.
set -u
R=${RUN_DIR:?output directory}
W=${WORKTREE:?clean checkout of the qualified source}
S=${INPUTS:?directory with survey_list.txt and ehalias_survey_test4.rs}
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
  grep -E '^test .* FAILED$' $R/mutation/$name.log | sed "s/^/$name killed-by: /" >> $R/mutation/summary.txt
}
F=crates/trust-cg-codegen/src/link_driver.rs
LIB='cargo test --locked --offline -j 16 -p trust-cg-codegen --lib -- link_driver::'
mutant no-window-fast-path $F '    if high - low <= modulus {
        return Ok(None);
    }' '    if std::hint::black_box(false) && high - low <= modulus {
        return Ok(None);
    }' "$LIB"
mutant no-step-bound $F '        if *work == CHECK_WORK_BOUND {' '        if std::hint::black_box(false) && *work == CHECK_WORK_BOUND {' "$LIB"
mutant candidates-miss-the-last $F '        while alias < last.1 {' '        while alias + modulus < last.1 {' "$LIB"
mutant candidates-skip-the-first $F '        let mut alias = lowest(u128::from(first.0));' '        let mut alias = lowest(u128::from(first.0)) + modulus;' "$LIB"
mutant name-needs-a-nul $F 'matches!(rest.get(wanted.len()), None | Some(0))' 'rest.get(wanted.len()) == Some(&0)' "$LIB"
mutant name-prefix-matches $F '                        && matches!(rest.get(wanted.len()), None | Some(0))' '                        && std::hint::black_box(true)' "$LIB"
mutant function-name-unbounded $F 'rest[..rest.len().min(4096)]' 'rest[..]' "$LIB"
mutant overlaps-first-entry $F '.map(|table| table.iter().copied().collect())' '.map(|table| table.iter().rev().copied().collect())' "$LIB"
mutant bound-per-pointer $F '            eh_wrap_alias(&self.backed, pointer, width, &mut self.alias_work)?' '            eh_wrap_alias(&self.backed, pointer, width, &mut 0)?' "$LIB"
mutant fde-bound-per-pointer $F '            &mut self.alias_work,
        )? {' '            &mut 0,
        )? {' "$LIB"
mutant placeholder-window-one-short $F 'contents[..contents.len().min(allowed + 1)]' 'contents[..contents.len().min(allowed)]' "$LIB"
mutant placeholder-scan-unbounded $F '            if contents.len() > allowed {' '            if std::hint::black_box(false) && contents.len() > allowed {' "$LIB"
mutant placeholder-scan-not-counted $F '            zeros += contents.len();' '            zeros += std::hint::black_box(0);' "$LIB"
mutant placeholder-nonzero-not-chosen $F '                .any(|byte| *byte != 0)
            {' '                .any(|byte| *byte != 0)
                && std::hint::black_box(false)
            {' "$LIB"
mutant placeholder-first-byte-only $F 'contents[..contents.len().min(allowed + 1)]' 'contents[..contents.len().min(allowed + 1).min(1)]' "$LIB"
mutant placeholder-unreadable-skipped $F '            let Some(contents) = image.bytes(section.offset, section.size) else {
                hdr_section = Some(section);
                break;
            };' '            let Some(contents) = image.bytes(section.offset, section.size) else {
                continue;
            };' "$LIB"
# Host survey (temporary ignored unit test, not committed).
cp $S/ehalias_survey_test4.rs $R/survey/survey_test.rs
WORKTREE=$W INPUTS=$S python3 - <<'PY'
import os
p=os.environ['WORKTREE']+'/crates/trust-cg-codegen/src/link_driver.rs'
s=open(p).read()
anchor='    /// The other address a narrow field\'s bits give: the lowest one, above'
t=open(os.environ['INPUTS']+'/ehalias_survey_test4.rs').read()
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
