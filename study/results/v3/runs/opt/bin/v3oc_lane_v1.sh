#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3oc_lane_v1.sh (v3 components, R2 single-option controls): run as ntbuild inside one scope. For each line
# NAME PKG of LIST: the facts that the combined options run v3o-NAME converted (PROVED there and listed in v3u-NAME) are
# written to $NT_BOX/results/v3ocsel-NAME.ax.tsv, and each is checked again with one option alone, as four driver
# runs: v3oc-NAME (csimp := true), v3os-NAME (stage := true), v3op-NAME (propSplit := true) and v3o16-NAME (--split 16),
# JOBS facts at a time, per fact 900 s and 48 GB, with the library root that v3o_lane_v2.sh uses.
# usage: v3oc_lane_v1.sh LIST JOBS
set -u
LIST=${1:?}; J=${2:?}
case "$J" in *[!0-9]*) echo "bad jobs"; exit 2;; esac
R=${NT_BOX}/results; LOGD=${NT_BOX}/v3/opt/logs; LOG=$LOGD/v3oc_lane.log
mkdir -p $LOGD || exit 3
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=1
echo "$(date -u +%FT%TZ) controls start list=$LIST jobs=$J" >> $LOG
while read -r name pkg; do
  [ -n "${name:-}" ] || continue
  case "$name" in *[!A-Za-z0-9_.-]*) echo "$(date -u +%FT%TZ) bad name $name" >> $LOG; continue;; esac
  [ -s "$R/v3o-$name.ax.tsv" ] && [ -s "$R/v3u-$name.ax.tsv" ] || { echo "$(date -u +%FT%TZ) $name: no v3o/v3u, skipped" >> $LOG; continue; }
  SEL=$R/v3ocsel-$name.ax.tsv
  if [ ! -e "$SEL" ]; then
    awk -F'\t' 'FNR==NR{u[$2 FS $3]=1; next} $6=="PROVED" && (($2 FS $3) in u) && !seen[$2 FS $3]++' "$R/v3u-$name.ax.tsv" "$R/v3o-$name.ax.tsv" > "$SEL.part" && mv "$SEL.part" "$SEL"
  fi
  n=$(wc -l < "$SEL" 2>/dev/null || echo 0)
  if [ "${n:-0}" -eq 0 ]; then echo "$(date -u +%FT%TZ) $name: nothing converted by the options, skipped" >> $LOG; continue; fi
  tc=$(cut -d: -f2 "$pkg/lean-toolchain" 2>/dev/null)
  if [ -n "$tc" ] && [ -f "${NT_BOX}/nt_fix14/$tc/.lake/build/lib/lean/NativeTrust.olean" ]; then root=${NT_BOX}/nt_fix14
  elif [ -n "$tc" ] && [ -f "${NT_BOX}/v3/nt_v15/$tc/.lake/build/lib/lean/NativeTrust.olean" ]; then root=${NT_BOX}/v3/nt_v15
  else echo "$(date -u +%FT%TZ) $name: no NativeTrust build for '$tc', skipped" >> $LOG; continue; fi
  for k in c s p 16; do
    case $k in c) opt=(--extra-config 'csimp := true');; s) opt=(--extra-config 'stage := true');;
      p) opt=(--extra-config 'propSplit := true');; 16) opt=(--split 16);; esac
    run=v3o$k-$name
    echo "$(date -u +%FT%TZ) start $run ($n facts, ${opt[*]})" >> $LOG
    python3 -u ${NT_BOX}/v3/m2_axioms5.py "$run" "$pkg" --skip-build --nt-root "$root" --jobs $J "${opt[@]}" \
      --from-results "v3ocsel-$name" > "$LOGD/$run.out" 2>&1
    rc=$?
    echo "$(date -u +%FT%TZ) end $run rc=$rc $(tail -1 $LOGD/$run.out)" >> $LOG
  done
done < "$LIST"
echo "$(date -u +%FT%TZ) controls end" >> $LOG
