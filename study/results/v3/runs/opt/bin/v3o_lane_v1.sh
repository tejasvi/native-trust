#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3o_lane_v1.sh (v3 components, R2 opt-in options): run as ntbuild inside one scope. For each line NAME PKG
# of LIST: if missing, writes the unconverted list v3u-NAME (v3u_list_v1.sh), then runs the study driver copy with the
# final library and v2's largest option set (stage, csimp, propSplit, --split 16) on those facts, run name v3o-NAME,
# JOBS facts at a time, per fact 900 s and 48 GB as the default run. Packages whose list is empty are skipped.
# usage: v3o_lane_v1.sh LIST JOBS
set -u
LIST=${1:?}; J=${2:?}
case "$J" in *[!0-9]*) echo "bad jobs"; exit 2;; esac
R=${NT_BOX}/results; BIN=${NT_BOX}/v3/opt/bin; LOGD=${NT_BOX}/v3/opt/logs; LOG=$LOGD/v3o_lane.log
mkdir -p $LOGD || exit 3
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=1
echo "$(date -u +%FT%TZ) lane start list=$LIST jobs=$J" >> $LOG
while read -r name pkg; do
  [ -n "${name:-}" ] || continue
  case "$name" in *[!A-Za-z0-9_.-]*) echo "$(date -u +%FT%TZ) bad name $name" >> $LOG; continue;; esac
  [ -d "$pkg" ] || { echo "$(date -u +%FT%TZ) $name: no dir $pkg" >> $LOG; continue; }
  [ -e "$R/v3u-$name.ax.tsv" ] || bash $BIN/v3u_list_v1.sh "$name" >> $LOG 2>&1
  n=$(wc -l < "$R/v3u-$name.ax.tsv" 2>/dev/null || echo 0)
  if [ "${n:-0}" -eq 0 ]; then echo "$(date -u +%FT%TZ) $name: nothing unconverted, skipped" >> $LOG; continue; fi
  echo "$(date -u +%FT%TZ) start v3o-$name ($n facts)" >> $LOG
  python3 -u ${NT_BOX}/v3/m2_axioms5.py "v3o-$name" "$pkg" --skip-build --nt-root ${NT_BOX}/nt_fix14 --jobs $J \
    --split 16 --extra-config 'stage := true, csimp := true, propSplit := true' --from-results "v3u-$name" \
    > "$LOGD/v3o-$name.out" 2>&1
  rc=$?
  echo "$(date -u +%FT%TZ) end v3o-$name rc=$rc $(tail -1 $LOGD/v3o-$name.out)" >> $LOG
done < "$LIST"
echo "$(date -u +%FT%TZ) lane end" >> $LOG
