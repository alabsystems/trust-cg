#!/bin/sh
# row.sh NAME LINKER RUNMODE ARGS... : run the driver ($TCG) with the
# linker (gnu, gold, lld), keep a sentinel in the output first, and on
# install run the program (RUNMODE exe), or a user linked against it
# (RUNMODE lib:<userobj>), or nothing (RUNMODE none).
R=$(cd "$(dirname "$0")" && pwd)
TCG=${TCG:?set TCG}
cd "$R" || exit 2
for v in $(env | grep -o '^TCG_[A-Z0-9_]*'); do [ "$v" = TCG ] || unset "$v"; done
mkdir -p lt lld-cc gold-cc out
[ -e lt/ld.lld ] || ln -sf "${LLD:?set LLD to an ld.lld}" lt/ld.lld
printf '#!/bin/sh\nexec /usr/bin/cc -fuse-ld=lld -B%s/lt/ "$@"\n' "$R" > lld-cc/cc
printf '#!/bin/sh\nexec /usr/bin/cc -fuse-ld=gold "$@"\n' > gold-cc/cc
chmod +x lld-cc/cc gold-cc/cc
name=$1; linker=$2; mode=$3; shift 3
P=$PATH
[ "$linker" = lld ] && P="$R/lld-cc:$PATH"
[ "$linker" = gold ] && P="$R/gold-cc:$PATH"
echo sentinel > "out/$name"
PATH=$P timeout 600 "$TCG" --format=text -o "out/$name" "$@" > "out/$name.log" 2>&1
drc=$?
if [ $drc -ne 0 ]; then
  tags=$(grep -o '\[TCG-[A-Z0-9-]*\]' "out/$name.log" | sort -u | tr '\n' ' ')
  kept=$(head -c 8 "out/$name")
  echo "$name [$linker] REFUSED rc=$drc $tags(output kept: $kept)"
  exit 0
fi
case $mode in
  none) echo "$name [$linker] INSTALLED (not run)"; exit 0;;
  lib:*) u=${mode#lib:}; PATH=$P cc -o "out/u_$name" "$u" "out/$name" -Wl,-rpath,"$R/out" > "out/u_$name.log" 2>&1 || { echo "$name [$linker] INSTALLED; user link failed"; exit 0; }; run="out/u_$name";;
  *) run="out/$name";;
esac
res=$(timeout 10 "$run" 2>&1 | tr '\n' ' '); rc=$(timeout 10 "$run" > /dev/null 2>&1; echo $?)
echo "$name [$linker] INSTALLED run: ${res}exit=$rc"
