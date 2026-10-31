#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3pkg_chain_v1.sh (v3 components): run as ntbuild inside one scope. For each package of LIST (lines
# NAME PKG [ADDON:MODS ...]): the options run and its controls (v3o_chainlist_v2.sh on a one-line list written to
# $NT_BOX/v3/opt/lists/), then each add-on of the line (v3a_chain_v2.sh), JOBS facts at a time. One package at a
# time, in the order of LIST.
# usage: v3pkg_chain_v1.sh LIST JOBS
set -u
L=${1:?}; J=${2:?}
case "$J" in *[!0-9]*) echo "bad jobs"; exit 2;; esac
B=${NT_BOX}/v3/opt/bin; LD=${NT_BOX}/v3/opt/lists
[ -s "$L" ] || { echo "missing $L"; exit 3; }
mkdir -p "$LD" || exit 3
while read -r name pkg addons; do
  [ -n "${name:-}" ] || continue
  case "$name" in *[!A-Za-z0-9_.-]*) echo "bad name $name"; continue;; esac
  printf '%s %s\n' "$name" "$pkg" > "$LD/one-$name.txt" || continue
  echo "$(date -u +%FT%TZ) package $name: options and controls"
  bash $B/v3o_chainlist_v2.sh "$LD/one-$name.txt" "$J"
  if [ -n "${addons:-}" ]; then
    echo "$(date -u +%FT%TZ) package $name: add-ons $addons"
    bash $B/v3a_chain_v2.sh "$name" "$pkg" "$J" $addons
  fi
done < "$L"
echo "$(date -u +%FT%TZ) packages end"
