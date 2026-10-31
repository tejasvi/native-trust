#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3oh_run_v1.sh (v3 components, R2 heavy cases: reported separately, not a column): run as ntbuild inside a scope on
# the study machine. The facts of v3u-NAME that the combined options run v3o-NAME did not prove are written to
# $NT_BOX/results/RUNsel-NAME.ax.tsv and checked again with the same options (stage, csimp, propSplit, --split 16)
# and a per-fact limit of SECS seconds (48 GB as before), run name RUN-NAME, JOBS facts at a time, with the library root
# that v3o_lane_v2.sh uses. With PREPDIR and PREPMOD every check also imports PREPMOD (an olean in PREPDIR: the shared
# staging module of the zcash case).
# usage: v3oh_run_v1.sh RUN NAME PKG SECS JOBS [PREPDIR PREPMOD]     (RUN is v3oh or v3oz)
set -u
RUN=${1:?}; N=${2:?}; P=${3:?}; T=${4:?}; J=${5:?}; PD=${6:-}; PM=${7:-}
case "$RUN" in v3oh|v3oz) ;; *) echo "bad run"; exit 2;; esac
case "$N" in *[!A-Za-z0-9_.-]*) echo "bad name"; exit 2;; esac
case "$T$J" in *[!0-9]*) echo "bad secs/jobs"; exit 2;; esac
R=${NT_BOX}/results; LOGD=${NT_BOX}/v3/opt/logs; LOG=$LOGD/$RUN-$N.out
[ -s "$R/v3u-$N.ax.tsv" ] && [ -s "$R/v3o-$N.ax.tsv" ] || { echo "missing v3u/v3o-$N"; exit 3; }
[ -d "$P" ] || { echo "no dir $P"; exit 3; }
imp=()
if [ -n "$PD" ]; then
  case "$PM" in ''|*[!A-Za-z0-9_]*) echo "bad prep module"; exit 2;; esac
  [ -f "$PD/$PM.olean" ] || { echo "missing $PD/$PM.olean"; exit 3; }
  imp=(--extra-path "$PD" --extra-import "$PM")
fi
tc=$(cut -d: -f2 "$P/lean-toolchain" 2>/dev/null)
if [ -n "$tc" ] && [ -f "${NT_BOX}/nt_fix14/$tc/.lake/build/lib/lean/NativeTrust.olean" ]; then root=${NT_BOX}/nt_fix14
elif [ -n "$tc" ] && [ -f "${NT_BOX}/v3/nt_v15/$tc/.lake/build/lib/lean/NativeTrust.olean" ]; then root=${NT_BOX}/v3/nt_v15
else echo "no NativeTrust build for '$tc'"; exit 3; fi
SEL=$R/${RUN}sel-$N.ax.tsv
if [ ! -e "$SEL" ]; then
  awk -F'\t' 'FNR==NR{if ($6=="PROVED") p[$2 FS $3]=1; next} !(($2 FS $3) in p) && !seen[$2 FS $3]++' \
    "$R/v3o-$N.ax.tsv" "$R/v3u-$N.ax.tsv" > "$SEL.part" && mv "$SEL.part" "$SEL" || exit 4
fi
n=$(wc -l < "$SEL")
mkdir -p $LOGD || exit 3
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=1
echo "$(date -u +%FT%TZ) start $RUN-$N ($n facts, ${T}s, tc $tc, root $root, import ${PM:-none})" >> $LOG
[ "$n" -gt 0 ] || { echo "$(date -u +%FT%TZ) nothing to check" >> $LOG; exit 0; }
python3 -u ${NT_BOX}/v3/m2_axioms5.py "$RUN-$N" "$P" --skip-build --nt-root "$root" --jobs $J --fact-timeout $T \
  --split 16 --extra-config 'stage := true, csimp := true, propSplit := true' --from-results "${RUN}sel-$N" "${imp[@]}" \
  >> $LOG 2>&1
rc=$?
echo "$(date -u +%FT%TZ) end $RUN-$N rc=$rc" >> $LOG
exit $rc
