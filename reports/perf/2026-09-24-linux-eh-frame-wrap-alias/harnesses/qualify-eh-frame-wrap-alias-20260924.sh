#!/bin/bash
# Qualify fix/aarch64-eh-frame-wrap-alias on clean source: tests, direct
# reproducers (prior CLI vs this source), source mutants, host survey.
set -u
R=${RUN_DIR:?output directory}
W=${WORKTREE:?clean checkout of the qualified source}
S=${INPUTS:?directory with pad.s, start2.s, survey_list.txt and ehalias_survey_test.rs}
PKG=${PKG:?AY/Clean package prefix}
export PATH="$PKG/bin:$HOME/.cargo/bin:$PATH" CARGO_TARGET_DIR=${CARGO_TARGET_DIR:?target directory outside the checkout} CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0
rm -rf $R; mkdir -p $R/tests $R/direct $R/mutation $R/survey
cd $W
{ git rev-parse HEAD; git status --short; } > $R/source.txt
status() { echo "$1" >> $R/status.txt; }

# 1. Tests on clean source. The codegen lib runs without TCG_* controls (the
# identity-Core admission refuses unkeyed ambient compiler controls).
cargo test --locked --offline -j 16 -p trust-cg-codegen --lib > $R/tests/codegen-lib.log 2>&1; status "codegen-lib=$?"
export TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1
cargo test --locked --offline -j 16 -p trust-cg-cli --bins --test link_options --test output_paths -- --nocapture > $R/tests/cli.log 2>&1; status "cli=$?"
for t in e2e_aarch64_link_runtime e2e_aarch64_elf_tlsie e2e_aarch64_eh_linux e2e_aarch64_eh_catch aarch64_elf_cfi_differential e2e_aarch64_elf_link; do
  cargo test --locked --offline -j 16 -p trust-cg-codegen --test $t -- --nocapture > $R/tests/$t.log 2>&1; status "$t=$?"
done
unset TCG_REQUIRE_LLD TCG_REQUIRE_GOLD

# 2. Direct reproducers: the CLI built from 47b08253b (prior) and this source.
D=$R/direct/work; mkdir -p $D/lldbin $D/goldbin
cp ${PRIOR_CLI:?trust-cg built from the base source} $D/trust-cg-prior
cp $CARGO_TARGET_DIR/debug/trust-cg $D/trust-cg-fix
sha256sum $D/trust-cg-prior $D/trust-cg-fix | sed "s|$D/||" > $R/direct/clis.sha256
printf '#!/bin/sh\nexec /usr/bin/cc -fuse-ld=lld "$@"\n' > $D/lldbin/cc
printf '#!/bin/sh\nexec /usr/bin/cc -fuse-ld=gold "$@"\n' > $D/goldbin/cc
chmod +x $D/lldbin/cc $D/goldbin/cc
cp $W/tests/fixtures/trust_ir_binary_container/conformance/b1_scalars.tmbc $D/
cp $S/ehalias/pad.s $S/ehalias/start2.s $D/
cp $S/tc_try_elf.o $S/driver.o $D/
cd $D
cc -c pad.s -o pad.o && cc -c start2.s -o start2.o
{
for cli in prior fix; do
  for addr in 0x110010000 0x50010000; do
    printf 'SECTIONS { .tcgtext %s : { *input_0.o(.text .text.*) } } INSERT AFTER .eh_frame;\n' $addr > insert_$addr.ld
    printf 'SECTIONS {\n  .tcgtext %s : { *input_0.o(.text .text.*) }\n  .text 0x10000000 : { *(.text .text.*) }\n  .eh_frame_hdr 0x8fff0000 : { *(.eh_frame_hdr) }\n  .eh_frame 0x90000000 : { *(.eh_frame) }\n}\n' $addr > full_$addr.ld
    for linker in lld gold gnu; do
      out=fde_${cli}_${linker}_$addr; rm -f $out
      case $linker in
        lld) bin="$D/lldbin:"; args="-Wl,--section-start=.text=0x10000000,--section-start=.eh_frame=0x90000000,--section-start=.eh_frame_hdr=0x8fff0000,--no-dynamic-linker -Wl,-T,insert_$addr.ld";;
        gold) bin="$D/goldbin:"; args="-Wl,-T,full_$addr.ld";;
        gnu) bin=""; args="-Wl,--section-start=.text=0x10000000,--section-start=.eh_frame=0x90000000,--section-start=.eh_frame_hdr=0x8fff0000,--no-dynamic-linker -Wl,-T,insert_$addr.ld";;
      esac
      echo "=== $out: trust-cg --nostdlib --no-pie -o $out b1_scalars.tmbc -Wl,start2.o,pad.o $args"
      PATH="$bin$PATH" ./trust-cg-$cli --nostdlib --no-pie -o $out b1_scalars.tmbc -Wl,start2.o,pad.o $args 2>&1
      echo "exit=$?"
      if [ -e $out ]; then
        ./$out; echo "installed; run exit=$?"
        nm $out | grep -E ' (isize_add_one|tcg_pad)$'
        readelf --debug-dump=frames $out | grep ' FDE '
      else echo "no output"; fi
    done
  done
  printf 'SECTIONS { .gcc_except_table 0x100200100 : { *(.gcc_except_table .gcc_except_table.*) } } INSERT AFTER .bss;\n' > lsda_far.ld
  for linker in lld gnu; do
    for place in far near; do
      out=lsda_${cli}_${linker}_$place; rm -f $out
      bin=""; [ $linker = lld ] && bin="$D/lldbin:"
      args=""; [ $place = far ] && args="-Wl,-T,lsda_far.ld"
      echo "=== $out: trust-cg --no-pie -o $out b1_scalars.tmbc -Wl,tc_try_elf.o,driver.o,-lstdc++ $args"
      PATH="$bin$PATH" ./trust-cg-$cli --no-pie -o $out b1_scalars.tmbc -Wl,tc_try_elf.o,driver.o,-lstdc++ $args 2>&1
      echo "exit=$?"
      if [ -e $out ]; then ./$out 2>&1; echo "installed; run exit=$?"; else echo "no output"; fi
    done
  done
done
} > $R/direct/reproducers.txt 2>&1
rm -f $D/fde_* $D/lsda_* $D/*.o $D/trust-cg-prior $D/trust-cg-fix
cd $W

# 3. Source mutants: each applied, its killing tests run, then reverted.
mutant() { # name file python-old python-new tests...
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
LIB='cargo test --locked --offline -j 16 -p trust-cg-codegen --lib -- a_pointer_whose eh_wrap classifies_gold'
CLIT='TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1 cargo test --locked --offline -j 16 -p trust-cg-cli --test link_options -- eh_frame_pointer_whose'
EHC='TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1 cargo test --locked --offline -j 16 -p trust-cg-codegen --test e2e_aarch64_eh_catch -- an_lsda'
VEN='TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1 cargo test --locked --offline -j 16 -p trust-cg-codegen --test e2e_aarch64_link_runtime -- call26_beyond'
mutant no-wrap-alias crates/trust-cg-codegen/src/link_driver.rs \
  'fn eh_wrap_alias(spans: &[(u64, u128)], pointer: &EhPointer, extent: u64) -> Option<u64> {' \
  'fn eh_wrap_alias(spans: &[(u64, u128)], pointer: &EhPointer, extent: u64) -> Option<u64> {
    if std::hint::black_box(true) {
        return None;
    }' "$LIB" "$CLIT" "$EHC"
mutant self-alias crates/trust-cg-codegen/src/link_driver.rs \
  '        if alias == resolved {' '        if alias == resolved && std::hint::black_box(false) {' "$LIB" "$CLIT"
mutant extent-off-by-one crates/trust-cg-codegen/src/link_driver.rs \
  '        (alias + extent <= high)' '        (alias + extent <= high + 1)' "$LIB"
mutant fde-only crates/trust-cg-codegen/src/link_driver.rs \
  '        } else if let Some(alias) = eh_wrap_alias(&self.memory, pointer, width) {' \
  '        } else if let Some(alias) = eh_wrap_alias(&self.memory, pointer, width).filter(|_| false) {' "$LIB" "$EHC"
mutant no-gold-lld-classes crates/trust-cg-codegen/src/link_driver.rs \
  '        } else if (line.contains("relocation overflow in ")' \
  '        } else if (line.contains("relocation overflow in XX")' "$LIB"
mutant unpinned-text crates/trust-cg-codegen/tests/e2e_aarch64_link_runtime.rs \
  '"--section-start=.text=0x800000,--section-start=.tcg_far_text=0x20000000",' \
  '"--section-start=.tcg_far_text=0x20000000",' "$VEN"

# 4. Host survey with a temporary ignored unit test (not committed).
cp $S/ehalias_survey_test.rs $R/survey/survey_test.rs
WORKTREE=$W INPUTS=$S python3 - <<'PY'
import os
p=os.environ['WORKTREE']+'/crates/trust-cg-codegen/src/link_driver.rs'
s=open(p).read()
anchor='    /// The other address a narrow field\'s bits give: the lowest one, above'
t=open(os.environ['INPUTS']+'/ehalias_survey_test.rs').read()
assert s.count(anchor)==1
open(p,'w').write(s.replace(anchor,t+anchor))
PY
cp $S/survey_list.txt $R/survey/images.txt
TCG_EH_SURVEY_LIST=$R/survey/images.txt TCG_EH_SURVEY_OUT=$R/survey/verdicts.tsv cargo test --locked --offline -j 16 -p trust-cg-codegen --lib -- tmp_survey_wrap --ignored > $R/survey/survey.log 2>&1; status "survey=$?"
git checkout -- crates/trust-cg-codegen/src/link_driver.rs
awk -F'\t' '{split($2,a,"="); f+=a[2]; w+=($3!="wrapped=0"); v[$4]++} END {print "images", NR; print "fdes", f; print "images_with_wrapped_pointers", w; for (k in v) print "verdict[" (k==""?"pass":k) "]", v[k]}' $R/survey/verdicts.tsv | sort > $R/survey/summary.txt
{ git rev-parse HEAD; git status --short; } > $R/source-final.txt
status DONE
