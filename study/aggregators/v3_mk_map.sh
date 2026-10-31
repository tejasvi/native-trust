#!/bin/bash
# v3_mk_map.sh (mk_map_v3.sh of 2026-10-30): writes OUT = the column map v2 (MAP2) plus one options-column line per shard result file
# results/v3s-<study run name>.ax.tsv ("shards", the v3s runs). v3spilot-* files are measurements and stay out.
# usage: v3_mk_map.sh MAP2 RESULTS OUT   (OUT must not exist; MAP2 = v3_map.tsv up to its '# O: shards' line)
set -u
MAP2=${1:?}; R=${2:?}; OUT=${3:?}
[ -e "$OUT" ] && { echo "exists $OUT"; exit 1; }
{ cat "$MAP2"; echo "# O: shards (the v3s runs), one line per results/v3s-BASE.ax.tsv (added by v3_mk_map.sh)"
  for f in "$R"/v3s-*.ax.tsv; do [ -e "$f" ] || continue; b=${f##*/v3s-}; b=${b%.ax.tsv}; printf 'O\t%s\tv3s-%s\n' "$b" "$b"; done; } > "$OUT"
echo "$OUT: $(command grep -c '^O' "$OUT") shard lines"
