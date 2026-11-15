#!/bin/bash
# One ordinary link through the driver and the same link outside it.
#   case.sh LINKER MODE OPTS EXTRA_TCG
# LINKER: bfd|lld|gold.  MODE: see below.  OPTS: a -Wl group without the
# "-Wl," prefix, or "none".  EXTRA_TCG: extra trust-cg flags or "none".
# Writes res/<name>.res with one line:
#   PASS | BADRUN | LINKFAIL(linker refused; raw also fails) |
#   FALSE?(driver refused, raw link runs OK) | TRUEREF(driver refused, raw runs bad)
W=${W:-$(cd "$(dirname "$0")" && pwd)}
TCG=${TCG:?set TCG}
L=$1; M=$2; O=$3; X=$4
cd "$W" || exit 2
case $L in
  lld) export PATH="$W/lld-cc:$PATH";;
  gold) export PATH="$W/gold-cc:$PATH";;
esac
name="${L}__${M}__$(printf '%s' "$O" | tr -c 'A-Za-z0-9=' '_' | cut -c1-50)_$(printf '%s' "$O" | md5sum | cut -c1-6)__$(printf '%s' "$X" | tr -c 'A-Za-z0-9' '_')"
out="out/$name"
mkdir -p out res
TF=""; RAWF=""; MAINW=""; USER=""; SRC=rich.trust_ir; RAWOBJ=rich.o; RM=""
case $M in
  pie) MAINW="cmain.o";;
  np) TF="--no-pie"; RAWF="-no-pie"; MAINW="cmain_nopie.o";;
  st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cmain_nopie.o";;
  cxx_pie) MAINW="cxxmain.o,-lstdc++";;
  cxx_np) TF="--no-pie"; RAWF="-no-pie"; MAINW="cxxmain.o,-lstdc++";;
  cxx_st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cxxmain.o,-lstdc++,-lm";;
  so) TF="--shared --relocation-model pic"; RAWF="-shared"; RAWOBJ=rich_pic.o; RM="--relocation-model pic"; USER="cmain.o";;
  so_full) TF="--shared --relocation-model pic"; RAWF="-shared"; RAWOBJ=rich_pic.o; RM="--relocation-model pic"; MAINW="cbpart_pic.o"; USER="cmain_nocb.o";;
  so_lto) TF="--shared --relocation-model pic"; RAWF="-shared"; RAWOBJ=rich_pic.o; RM="--relocation-model pic"; MAINW="cbpart_lto_pic.o"; USER="cmain_nocb.o";;
  lto_pie) if [ "$L" = lld ]; then MAINW="cmain_nocb.o,lto.bc"; else MAINW="cmain_lto.o"; fi;;
  lto_st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; if [ "$L" = lld ]; then MAINW="cmain_nocb.o,lto.bc"; else MAINW="cmain_lto.o"; fi;;
  lto_np) TF="--no-pie"; RAWF="-no-pie"; if [ "$L" = lld ]; then MAINW="cmain_nocb.o,lto.bc"; else MAINW="cmain_lto.o"; fi;;
  cxx_lto) MAINW="cxxmain_lto.o,-lstdc++";;
  ar) MAINW="cmain_nocb.o,libcb.a";;
  ar_st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cmain_nocb.o,libcb.a";;
  thin) MAINW="cmain_nocb.o,libcb_thin.a";;
  ar_lto) MAINW="cmain_nocb.o,libcb_lto.a";;
  fpic) MAINW="cmain_fpic.o";;
  dbg) MAINW="cmain_g.o";;
  bc_so) TF="--shared --relocation-model pic"; RAWF="-shared"; RM="--relocation-model pic"; MAINW="lto.bc"; USER="cmain_nocb.o";;
  bc_ar) MAINW="cmain_nocb.o,liblto_bc.a";;
  bc_ar_st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cmain_nocb.o,liblto_bc.a";;
  bc_thin_st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cmain_nocb.o,lto_thin.bc";;
  bc_thin) MAINW="cmain_nocb.o,lto_thin.bc";;
  bc_st_cxx) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cxxmain_nocb.o,lto.bc,-lstdc++,-lm";;
  evil_bc_ar_st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cmain_nocb.o,libevil_bc.a";;
  evil_elf_ar_st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cmain_nocb.o,libevil_elf.a";;
  evil_elf_st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cmain_nocb.o,evil_elf.o";;
  evil_bc_st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cmain_nocb.o,evil.bc";;
  evil2_bc_ar_st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cmain_nocb.o,libevil2_bc.a";;
  evil2_elf_ar_st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cmain_nocb.o,libevil2_elf.a";;
  evil2_bc_ar_cxx_st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cxxmain_nocb.o,libevil2_bc.a,-lstdc++,-lm";;
  evil2_elf_ar_cxx_st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cxxmain_nocb.o,libevil2_elf.a,-lstdc++,-lm";;
  evil2_lto_ar_st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cmain_nocb.o,libevil2_lto.a";;
  evil2_lto_st) TF="--static"; RAWF="-static -Wl,--eh-frame-hdr"; MAINW="cmain_nocb.o,evil2_lto.o";;
  dso) SRC=dso.trust_ir; TF="--rpath $W"; RAWF="-Wl,-rpath,$W"; MAINW="cmain_nocb.o,-L$W,-lcbdso";;
  dso_np) SRC=dso.trust_ir; TF="--no-pie --rpath $W"; RAWF="-no-pie -Wl,-rpath,$W"; MAINW="cmain_nocb.o,-L$W,-lcbdso";;
  dso_so) SRC=dso.trust_ir; TF="--shared --relocation-model pic --rpath $W"; RAWF="-shared -Wl,-rpath,$W"; RM="--relocation-model pic"; MAINW="-L$W,-lcbdso"; USER="cmain_nocb.o";;
  *) echo "unknown mode $M" >&2; exit 2;;
esac
O="${O//MAPNAME/$name}"
WL=""
if [ -n "$MAINW" ]; then WL="$MAINW"; fi
if [ "$O" != none ]; then
  if [ -n "$WL" ]; then WL="$WL,$O"; else WL="$O"; fi
fi
EX=""
if [ "$X" != none ]; then EX="${X//_/ }"; fi
if [ -n "$WL" ]; then WLARG="-Wl,$WL"; else WLARG=""; fi
# Through the driver.
$TCG --format=text $TF $EX -o "$out" $SRC $WLARG > "$out.log" 2>&1
drc=$?
# Outside the driver: same objects, same options.
$TCG --format=text $RM $EX -c -o "$out.rawobj.o" $SRC > /dev/null 2>&1
RAWOBJ_X="$out.rawobj.o"
cc $RAWF -o "$out.raw" -Wl,-z,noexecstack $RAWOBJ_X $WLARG > "$out.raw.log" 2>&1
rrc=$?
runit() {
  # $1 = image. Prints the run result line.
  if [ -n "$USER" ]; then
    cc -o "$1.user" $USER "$1" "-Wl,-rpath,$W/out,-rpath,$W" > "$1.user.log" 2>&1 || { echo "userlink-fail"; return; }
    # The user loads the library by its path name.
    r=$(timeout 20 "$1.user" 2>&1; echo "rc=$?")
  else
    r=$(timeout 20 "$1" 2>&1; echo "rc=$?")
  fi
  printf '%s' "$r" | tr '\n' ' '
}
tags=$(grep -o '\[TCG-[A-Z0-9-]*\]' "$out.log" | sort -u | tr '\n' ' ')
if [ $drc -eq 0 ]; then
  # The user of a shared library needs it under its link name.
  r=$(runit "$out")
  case "$r" in
    *"v=OK"*"rc=0"*) res="PASS";;
    *) res="BADRUN [$r]";;
  esac
else
  if [ $rrc -ne 0 ]; then
    res="LINKFAIL $tags $(grep -m1 -i -E 'error|refus' "$out.log" | cut -c1-200)"
  else
    r=$(runit "$out.raw")
    case "$r" in
      *"v=OK"*"rc=0"*) res="FALSE? $tags $(grep -m1 -i -E 'error|refus' "$out.log" | cut -c1-300)";;
      *) res="TRUEREF $tags [$r]";;
    esac
  fi
fi
echo "$name $res" > "res/$name.res"
echo "$name $res"
