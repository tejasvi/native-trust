#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run as ntbuild: process a per-axiom lane file (NAME<TAB>PKG<TAB>EXTRA_ARGS per line) one package at a time with m2_axioms3.py
LANE=$1; shift
while IFS=$'\t' read -r name pkg extra; do
  [ -n "$name" ] || continue
  echo "$(date -u +%FT%TZ) start $name $extra"
  # shellcheck disable=SC2086
  python3 -u ${NT_BOX}/m2_axioms3.py "$name" "$pkg" $extra "$@" > ${NT_BOX}/m2_$name.ax3.out 2>&1
  rc=$?
  echo "$(date -u +%FT%TZ) end $name rc=$rc $(tail -1 ${NT_BOX}/m2_$name.ax3.out)"
done < "$LANE"
