#!/bin/zsh
# Bounded single wait: until <file> contains <pattern> or no process matches <pgrep pattern> (the
# writer died), at most <seconds>. usage: waitfor.sh <seconds> <file> <pattern> <pgrep pattern>
END=$(( $(date +%s) + ${1:?secs} )); F=${2:?file}; P=${3:?pattern}; W=${4:?writer}
while [ $(date +%s) -lt $END ]; do
  grep -qE "$P" "$F" 2>/dev/null && { echo "MATCHED"; exit 0; }
  pgrep -f "$W" >/dev/null || { sleep 2; grep -qE "$P" "$F" 2>/dev/null && { echo "MATCHED"; exit 0; }; echo "WRITER-GONE"; exit 2; }
  sleep 15
done
echo "STILL-RUNNING"; exit 1
