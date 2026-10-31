#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3u_batch_v1.sh (v3 components): run as ntbuild in a small scope. Writes the unconverted list v3u-NAME
# (v3u_list_v2.sh) for every package NAME of LIST (first column) that has none yet.
# usage: v3u_batch_v1.sh LIST
set -u
L=${1:?}
[ -s "$L" ] || { echo "missing $L"; exit 3; }
while read -r name rest; do
  [ -n "${name:-}" ] || continue
  if [ -e "${NT_BOX}/results/v3u-$name.ax.tsv" ]; then echo "$name: v3u exists"; continue; fi
  bash ${NT_BOX}/v3/opt/bin/v3u_list_v2.sh "$name"
done < "$L"
