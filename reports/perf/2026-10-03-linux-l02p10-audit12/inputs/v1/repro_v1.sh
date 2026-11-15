#!/bin/sh
# The first verifier's reproducers of the twelfth-audit repair (be368f243),
# and the third class its repair found, each through the driver ($TCG) with
# the output's sentinel kept on refusal, and outside it where the row shows
# the defect.
# Usage: TCG=<trust-cg> LLD=<ld.lld> sh repro_v1.sh. It writes its objects
# and programs into its own directory, so run it on a copy of `inputs/`.
# Inputs: this directory, and ../tls.trust_ir, ../const.trust_ir,
# ../valstart.c and ../cdat.c.
R=$(cd "$(dirname "$0")" && pwd)
cd "$R" || exit 2
export TCG=${TCG:?set TCG} LLD=${LLD:?set LLD to an ld.lld}
for f in tls.trust_ir const.trust_ir valstart.c cdat.c; do cp ../$f .; done
python3 make_scripts.py || exit 2
cc -c -O1 -fPIE -fno-stack-protector -ffreestanding -o cstart3.o cstart3.c
cc -c -O1 -fPIE -fno-stack-protector -ffreestanding -o cstart.o cstart.c
cc -c -O1 -fno-pic -ffreestanding -o valstart.o valstart.c
cc -c -O1 -fpic -o cdat.o cdat.c
cc -c -O1 -o btmain.o btmain.c
"$TCG" --format=text -c -o tls_tcg.o tls.trust_ir > /dev/null
"$TCG" --format=text -c -o const.o const.trust_ir > /dev/null
"$TCG" --format=text -c -o val2.o val2.trust_ir > /dev/null
"$TCG" --format=text -c -o tlsonly.o tlsonly.trust_ir > /dev/null
echo "== V1-1: -z nosectionheader skipped the thread-local section rules"
./row.sh D3c_ok gnu exe --nostdlib tls.trust_ir -Wl,cstart3.o
./row.sh D3_tbssfirst gnu exe --nostdlib tls.trust_ir -Wl,cstart3.o,-T,tbssfirst_pie.ld
./row.sh D3_tbssfirst_nsh gnu exe --nostdlib tls.trust_ir -Wl,cstart3.o,-T,tbssfirst_pie.ld,-z,nosectionheader
./row.sh C0_ok gnu exe --nostdlib tlsonly.trust_ir -Wl,cstart.o
./row.sh C2_bad gnu exe --nostdlib tlsonly.trust_ir -Wl,cstart.o,cdat.o,-T,datatls_pie_al.ld
./row.sh C1_bad_nsh gnu exe --nostdlib tlsonly.trust_ir -Wl,cstart.o,cdat.o,-T,datatls_pie_al.ld,-z,nosectionheader
cc -nostdlib -o out/D3_raw cstart3.o tls_tcg.o -Wl,-T,tbssfirst_pie.ld,-z,nosectionheader
echo "D3_raw exit=$(out/D3_raw; echo $?) (42: tcg_tz reads tcg_t's 42)"
echo "== V1-2: trust-cg's .eh_frame in a PT_LOAD without PF_R"
for sc in dyneh0 dyneh4; do for L in gnu lld gold; do
  ./row.sh F_${sc}_$L $L exe --no-pie const.trust_ir -Wl,btmain.o,-T,$sc.ld
done; done
for L in gnu lld gold; do
  P=$PATH; [ "$L" = lld ] && P="$R/lld-cc:$PATH"; [ "$L" = gold ] && P="$R/gold-cc:$PATH"
  PATH=$P cc -no-pie -o out/F_raw_$L btmain.o const.o -Wl,-T,dyneh0.ld
  echo "F_raw_$L exit=$(out/F_raw_$L > /dev/null 2>&1; echo $?) (139: SIGSEGV)"
done
echo "== R1-3: trust-cg's sections not loaded where the map places them"
for L in gnu lld gold; do
  ./row.sh N_ronl_$L $L exe --static --nostdlib const.trust_ir -Wl,valstart.o,-T,ronl.ld
done
for L in gnu lld; do
  ./row.sh N_none_nsh_$L $L exe --static --nostdlib val2.trust_ir -Wl,valstart.o,--eh-frame-hdr,-T,datanone.ld,-z,nosectionheader
done
for L in gnu lld gold; do
  P=$PATH; [ "$L" = lld ] && P="$R/lld-cc:$PATH"; [ "$L" = gold ] && P="$R/gold-cc:$PATH"
  PATH=$P cc -static -nostdlib -o out/N_ronl_raw_$L valstart.o const.o -Wl,-T,ronl.ld
  echo "N_ronl_raw_$L exit=$(out/N_ronl_raw_$L; echo $?) (50: tcg_c reads 0)"
  [ "$L" = gold ] && continue
  PATH=$P cc -static -nostdlib -o out/N_none_raw_$L valstart.o val2.o -Wl,--eh-frame-hdr,-T,datanone.ld,-z,nosectionheader
  echo "N_none_raw_$L exit=$(out/N_none_raw_$L; echo $?) (50: tcg_val reads 0)"
done
