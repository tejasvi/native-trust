#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run as ntbuild: process a lane file (NAME<TAB>PKG per line) one package at a time
LANE=$1; shift
while IFS=$'\t' read -r name pkg; do
  [ -n "$name" ] || continue
  echo "$(date -u +%FT%TZ) start $name"
  python3 -u ${NT_BOX}/m2_repo.py "$name" "$pkg" "$@" > ${NT_BOX}/m2_$name.out 2>&1
  echo "$(date -u +%FT%TZ) end $name rc=$? $(tail -1 ${NT_BOX}/m2_$name.out)"
done < "$LANE"
