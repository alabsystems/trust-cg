#!/bin/sh
# L02-P10 twelfth-audit reproducers (TLS template, segment permissions, LLVM
# bitcode), each run through the driver ($TCG) and, where it shows the
# defect, outside it. Usage: TCG=<trust-cg> repro_all.sh > out.txt
R=$(cd "$(dirname "$0")" && pwd)
# LLVM: the Trust package's LLVM tools (llvm-as, opt, llc, llvm-ar);
# LLD: an ld.lld 22.1.6.
LLVM=${LLVM:?set LLVM to <trust sysroot>/lib/rustlib/aarch64-unknown-linux-gnu/bin}
LLD=${LLD:?set LLD to an ld.lld}
TCG=${TCG:?set TCG}
cd "$R" || exit 2
for v in $(env | grep -o '^TCG_[A-Z0-9_]*'); do [ "$v" = TCG ] || unset "$v"; done
mkdir -p lt lld-cc gold-cc out
ln -sf "$LLD" lt/ld.lld
printf '#!/bin/sh\nexec /usr/bin/cc -fuse-ld=lld -B%s/lt/ "$@"\n' "$R" > lld-cc/cc
printf '#!/bin/sh\nexec /usr/bin/cc -fuse-ld=gold "$@"\n' > gold-cc/cc
chmod +x lld-cc/cc gold-cc/cc
cc -c -O1 -o tlsmain.o tlsmain.c
cc -c -O1 -o user.o user.c
cc -c -O1 -fpic -o cdat.o cdat.c
cc -c -O1 -fno-pic -ffreestanding -o valstart.o valstart.c
cc -c -O2 -o cmain_nocb.o cmain_nocb.c
"$LLVM"/llvm-as -o evil2.bc evil2.ll
"$LLVM"/llc -filetype=obj -relocation-model=pic -o evil2_elf.o evil2.ll
rm -f libevil2_bc.a libevil2_elf.a liblto_bc.a
"$LLVM"/llvm-ar rcs libevil2_bc.a evil2.bc
ar rcs libevil2_elf.a evil2_elf.o
"$LLVM"/llvm-as -o lto.bc lto.ll
"$LLVM"/opt --thinlto-bc -o lto_thin.bc lto.ll
"$LLVM"/llvm-ar rcs liblto_bc.a lto.bc
"$TCG" --format=text -c -o tls_tcg.o tls.trust_ir > /dev/null
"$TCG" --format=text -c -o const.o const.trust_ir > /dev/null
"$TCG" --format=text -c -o rich.o rich.trust_ir > /dev/null
"$TCG" --format=text --relocation-model pic -c -o tlsgd.o tlsgd.trust_ir > /dev/null
# row NAME LINKER EXPECT ARGS...: EXPECT is refuse or install.
row() {
  name=$1; linker=$2; expect=$3; shift 3
  P=$PATH
  [ "$linker" = lld ] && P="$R/lld-cc:$PATH"
  [ "$linker" = gold ] && P="$R/gold-cc:$PATH"
  echo sentinel > "out/$name"
  PATH=$P timeout 600 "$TCG" --format=text -o "out/$name" "$@" > "out/$name.log" 2>&1
  drc=$?
  if [ $drc -ne 0 ]; then
    tags=$(grep -o '\[TCG-[A-Z0-9-]*\]' "out/$name.log" | sort -u | tr '\n' ' ')
    kept=$(head -c 8 "out/$name")
    echo "$name [$linker] REFUSED rc=$drc $tags(output kept: $kept) expect=$expect"
    return
  fi
  case $name in
    lib*) PATH=$P cc -o "out/u_$name" user.o "out/$name" -Wl,-rpath,"$R/out"; run="out/u_$name";;
    *) run="out/$name";;
  esac
  res=$(timeout 10 "$run" 2>&1 | tr '\n' ' '); rc=$(timeout 10 "$run" > /dev/null 2>&1; echo $?)
  echo "$name [$linker] INSTALLED run: ${res}exit=$rc expect=$expect"
}
echo "== TLS template (skeptic 1)"
row T0_gnu_full_nopie gnu install --no-pie tls.trust_ir -Wl,tlsmain.o,-T,ph_full.ld
row T0_gnu_full_pie gnu install tls.trust_ir -Wl,tlsmain.o,-T,phpie_full.ld
row T1_gnu_tbss_nopie gnu refuse --no-pie tls.trust_ir -Wl,tlsmain.o,-T,ph_tbss.ld
row T1_gnu_tbss_pie gnu refuse tls.trust_ir -Wl,tlsmain.o,-T,phpie_tbss.ld
row T2_lld_pie lld refuse tls.trust_ir -Wl,tlsmain.o,-z,norelro,-T,split.ld
row libT4_lld.so lld refuse --shared --relocation-model pic tlsgd.trust_ir -Wl,cdat.o,-z,norelro,-T,splitall.ld
row T5_lld_nopie lld refuse --no-pie tls.trust_ir -Wl,tlsmain.o,--section-start=.tbss=0x700000
row T5_lld_pie lld refuse tls.trust_ir -Wl,tlsmain.o,--section-start=.tbss=0x700000
for L in gnu gold lld; do
  row Tok_${L}_pie $L install tls.trust_ir -Wl,tlsmain.o
  row Tok_${L}_nopie $L install --no-pie tls.trust_ir -Wl,tlsmain.o
  row Tok_${L}_static $L install --static tls.trust_ir -Wl,tlsmain.o
  row Tok_${L}_relro_now $L install tls.trust_ir -Wl,tlsmain.o,-z,relro,-z,now
  row libTok_${L}.so $L install --shared --relocation-model pic tlsgd.trust_ir -Wl,cdat.o
done
echo "== TLS raw links outside the driver"
for spec in "T1_gnu_tbss_nopie_raw|gnu|-no-pie tlsmain.o tls_tcg.o -Wl,-T,ph_tbss.ld" \
            "T5_lld_nopie_raw|lld|-no-pie tlsmain.o tls_tcg.o -Wl,--section-start=.tbss=0x700000" \
            "T2_lld_pie_raw|lld|tlsmain.o tls_tcg.o -Wl,-z,norelro,-T,split.ld"; do
  n=${spec%%|*}; rest=${spec#*|}; l=${rest%%|*}; a=${rest#*|}
  P=$PATH; [ "$l" = lld ] && P="$R/lld-cc:$PATH"
  # shellcheck disable=SC2086
  PATH=$P cc -o "out/$n" $a > "out/$n.log" 2>&1 && echo "$n: $(out/$n | tr '\n' ' ')exit=$(out/$n > /dev/null; echo $?)"
done
echo "== Segment permissions (auditor C13)"
for L in gnu lld; do
  row P_ro0_$L $L refuse --static --nostdlib const.trust_ir -Wl,valstart.o,-T,ro0.ld
  row P_ro4_$L $L install --static --nostdlib const.trust_ir -Wl,valstart.o,-T,ro4.ld
  row P_textro2_$L $L refuse --static --nostdlib const.trust_ir -Wl,valstart.o,-T,textro2.ld
done
for L in gnu lld; do
  P=$PATH; [ "$L" = lld ] && P="$R/lld-cc:$PATH"
  for s in ro0 ro4 textro2; do
    PATH=$P cc -static -nostdlib -o "out/P_${s}_${L}_raw" valstart.o const.o -Wl,-T,$s.ld > /dev/null 2>&1 && echo "P_${s}_${L}_raw exit=$(out/P_${s}_${L}_raw; echo $?)"
  done
done
echo "== LLVM bitcode (skeptic 2)"
row R1_bc lld refuse --static rich.trust_ir -Wl,cmain_nocb.o,libevil2_bc.a
row R1_elf lld refuse --static rich.trust_ir -Wl,cmain_nocb.o,libevil2_elf.a
row R2_bc lld install --static rich.trust_ir -Wl,cmain_nocb.o,lto.bc
row R2_thin lld install --static rich.trust_ir -Wl,cmain_nocb.o,lto_thin.bc
row R2_bc_ar lld install --static rich.trust_ir -Wl,cmain_nocb.o,liblto_bc.a
row R2_bc_pie lld install rich.trust_ir -Wl,cmain_nocb.o,lto.bc
row R2_bc_nopie lld install --no-pie rich.trust_ir -Wl,cmain_nocb.o,lto.bc
mkdir -p cache
row R2_thin_cache lld refuse --static rich.trust_ir -Wl,cmain_nocb.o,lto_thin.bc,--thinlto-cache-dir=cache
row R2_thin_cache2 lld refuse --static rich.trust_ir -Wl,cmain_nocb.o,lto_thin.bc,--thinlto-cache-dir=cache
P="$R/lld-cc:$PATH"
PATH=$P cc -static -o out/R1_bc_raw rich.o cmain_nocb.o libevil2_bc.a > /dev/null 2>&1 && echo "R1_bc_raw: exit=$(timeout 5 out/R1_bc_raw > /dev/null 2>&1; echo $?) (124 = hung)"
PATH=$P cc -static -o out/R2_bc_raw rich.o cmain_nocb.o lto.bc > /dev/null 2>&1 && echo "R2_bc_raw: $(out/R2_bc_raw | tr '\n' ' ')exit=$(out/R2_bc_raw > /dev/null; echo $?)"
