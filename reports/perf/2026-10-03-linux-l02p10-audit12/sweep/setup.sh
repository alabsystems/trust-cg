#!/bin/sh
# Inputs for the ordinary-link sweep (skeptic #2, L02-P10, 23ee1104a).
set -e
W=${W:-$(cd "$(dirname "$0")" && pwd)}
TCG=${TCG:?set TCG}
LLVM=${LLVM:?set LLVM to <trust sysroot>/lib/rustlib/aarch64-unknown-linux-gnu/bin}
cd "$W"
mkdir -p lld-tools lld-cc gold-cc
ln -sf "${LLD:?set LLD to an ld.lld}" lld-tools/ld.lld
printf '#!/bin/sh\nexec /usr/bin/cc -fuse-ld=lld -B%s/lld-tools/ "$@"\n' "$W" > lld-cc/cc
printf '#!/bin/sh\nexec /usr/bin/cc -fuse-ld=gold "$@"\n' > gold-cc/cc
chmod +x lld-cc/cc gold-cc/cc
cc -c -O2 -o cmain.o cmain.c
cc -c -O2 -g -o cmain_g.o cmain.c
cc -c -O2 -fPIC -o cmain_pic.o cmain.c
cc -c -O2 -fpic -o cmain_fpic.o cmain.c
cc -c -O2 -fno-pie -o cmain_nopie.o cmain.c
cc -c -O2 -flto -o cmain_lto.o cmain.c
cc -c -O2 -o cmain_nocb.o cmain_nocb.c
cc -c -O2 -flto -o cmain_nocb_lto.o cmain_nocb.c
cc -c -O2 -o cbpart.o cbpart.c
cc -c -O2 -fPIC -o cbpart_pic.o cbpart.c
cc -c -O2 -flto -o cbpart_lto.o cbpart.c
cc -c -O2 -flto -fPIC -o cbpart_lto_pic.o cbpart.c
rm -f libcb.a libcb_lto.a libcb_thin.a
ar rcs libcb.a cbpart.o
gcc-ar rcs libcb_lto.a cbpart_lto.o
ar rcsT libcb_thin.a cbpart.o
g++ -c -O2 -o cxxmain.o cxxmain.cc
g++ -c -O2 -flto -o cxxmain_lto.o cxxmain.cc
"$LLVM"/llvm-as -o lto.bc lto.ll
"$TCG" --format=text -c -o rich.o rich.trust_ir
"$TCG" --format=text --relocation-model pic -c -o rich_pic.o rich.trust_ir
# The inputs of case2.sh's bitcode, C-runtime replacement and DSO modes
# (made by hand in the second skeptic's round; reconstructed here).
g++ -c -O2 -o cxxmain_nocb.o cxxmain_nocb.cc
"$LLVM"/opt --thinlto-bc -o lto_thin.bc lto.ll
rm -f liblto_bc.a libevil_bc.a libevil_elf.a libevil2_bc.a libevil2_elf.a libevil2_lto.a
"$LLVM"/llvm-ar rcs liblto_bc.a lto.bc
for e in evil evil2; do
  "$LLVM"/llvm-as -o $e.bc $e.ll
  "$LLVM"/llc -filetype=obj -relocation-model=pic -o ${e}_elf.o $e.ll
  "$LLVM"/llvm-ar rcs lib${e}_bc.a $e.bc
  ar rcs lib${e}_elf.a ${e}_elf.o
done
cc -c -O2 -flto -o evil2_lto.o evil2.c
gcc-ar rcs libevil2_lto.a evil2_lto.o
cc -shared -fPIC -O2 -o libcbdso.so cbdso.c
echo setup-ok
