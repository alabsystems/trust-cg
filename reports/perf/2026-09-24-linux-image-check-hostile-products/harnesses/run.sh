#!/bin/bash
# Each hostile image through a release CLI whose fake linker copies it to
# the staging path: outcome, time, peak RSS, refusal codes, leftovers.
H=/tmp/claude-1000/-home-ayates-trust-cg/5c614a35-bd1c-42d4-a526-64c88f7a04db/scratchpad/hostile
cd "$H/cli" || exit 1
for img in "$@"; do
  name=$(basename "$img")
  cp --sparse=always "$img" "$H/cli/image.elf"
  rm -f prog out.txt
  ( ulimit -v 33554432
    HOSTILE_IMAGE="$H/cli/image.elf" PATH="$H/cli/bin:$PATH" timeout ${LIMIT:-1800} \
      /usr/bin/time -f "TIME %e s, peak RSS %M KiB, exit %x" \
      "$CLI" --nostdlib -o prog b1_scalars.tmbc > out.txt 2>&1 )
  codes=$(grep -oE "\[TCG-[A-Z0-9-]+\]" out.txt | sort | uniq -c | tr '\n' ' ')
  installed=no; [ -e prog ] && installed=yes
  left=$(ls -a | grep -c tcg-link)
  echo "=== $name: installed=$installed codes: ${codes:-none} leftovers=$left"
  grep -E "^TIME|Command terminated" out.txt
  grep -m1 -E "error\[link" out.txt | cut -c1-400
  rm -rf prog image.elf out.txt .tcg-link-*
done
