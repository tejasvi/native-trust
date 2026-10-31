#!/bin/bash
# v3ms_follow_v1.sh FOLLOW_FILE TAG   -- run as ntbuild in a systemd unit v3ms-*-sweeps (paper v3, sweep parts).
# FOLLOW_FILE lines: DEFAULT_RUN<TAB>RUN_NAME<TAB>PKG<TAB>DRIVER_ARGS  (driver = /home/ntbuild/v3/m2_axioms5.py)
# Each line starts only after its package's v3 default run has ended: a line "end DEFAULT_RUN rc=0" in one of the
# default lanes' logs /home/ntbuild/v3/logs/lane*.log. A default run that ended with rc != 0 is skipped, and so is a
# line whose selection in results/DEFAULT_RUN.ax.tsv is empty (plain: no PROVED outer fact; nocap: no FAILED/blocked
# fact). One driver at a time, in the order the default runs end (file order among those ready). The driver skips
# facts already in results/RUN_NAME.ax.tsv, so a restart resumes. Log: /home/ntbuild/v3/sweeps/logs/follow_TAG.log
set -u
FF=${1:?follow file}; TAG=${2:?tag}
M=/home/ntbuild/v3/sweeps; R=/home/ntbuild/results
LOG=$M/logs/follow_$TAG.log; OUT=$M/out
mkdir -p $M/logs $OUT
log() { echo "$(date -u +%FT%TZ) $*" >> "$LOG"; }
# selection size of a line in the default run's results (last row per fact), same rules as the driver
sel_count() {  # $1 default run, $2 driver args
  local f=$R/$1.ax.tsv v="" rs=""
  [ -f "$f" ] || { echo 0; return; }
  case " $2 " in *" --from-verdict PROVED "*) v=PROVED;; *" --from-verdict FAILED "*) v=FAILED;; esac
  case " $2 " in *" --from-reason blocked "*) rs=blocked;; esac
  awk -F'\t' -v v="$v" -v rs="$rs" 'NF >= 7 {last[$2 "\t" $3] = $6 "\t" $7 "\t" $5}
    END {n = 0; for (k in last) {split(last[k], c, "\t"); if ((v == "" || c[1] == v) && (rs == "" || c[2] == rs) && c[3] != "True") n++}; print n}' "$f"
}
mapfile -t LINES < <(awk -F'\t' 'NF >= 3 && $1 !~ /^#/' "$FF")
declare -A DONE
log "follow start $FF lines=${#LINES[@]} pid=$$"
while :; do
  left=0; started=0
  for i in "${!LINES[@]}"; do
    [ -n "${DONE[$i]:-}" ] && continue
    left=$((left + 1))
    IFS=$'\t' read -r dflt run pkg args <<< "${LINES[$i]}"
    e=$(awk -v d="$dflt" '$2 == "end" && $3 == d && $4 ~ /^rc=/ {r = $4} END {print r}' /home/ntbuild/v3/logs/lane*.log 2>/dev/null)
    [ -n "$e" ] || continue
    if [ "$e" != "rc=0" ]; then log "SKIP $run: $dflt ended $e"; DONE[$i]=1; continue; fi
    n=$(sel_count "$dflt" "$args")
    if [ "$n" = 0 ]; then log "SKIP $run: empty selection in $dflt"; DONE[$i]=1; continue; fi
    log "start $run (from $dflt, selection $n outer facts before --sample) args: $args"
    # shellcheck disable=SC2086
    python3 -u /home/ntbuild/v3/m2_axioms5.py "$run" "$pkg" $args > "$OUT/m2_$run.ax5.out" 2>&1
    rc=$?
    log "end $run rc=$rc $(tail -1 "$OUT/m2_$run.ax5.out" | cut -c1-200)"
    DONE[$i]=1; started=1
    break
  done
  [ "$left" -eq 0 ] && break
  [ "$started" -eq 1 ] || sleep 120
done
log "follow end $FF"
