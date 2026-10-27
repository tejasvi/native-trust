#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# usage (as ntbuild on the box): [MEMGB=32] [TO=7200] [OLEAN=1] [SLOTS="0 1 2"] [SLOTFILE=F] [MEMCHK_GB=G] lrun3.sh DIR NAME
# Compiles DIR/NAME.lean (to NAME.olean if OLEAN=1) with LEAN_PATH = NativeTrust nt_fix7 : work_parse_once/lib : DIR : berry-esseen.
# Slot locks work_parse_once/slots/slot<i>: one lean process per slot. SLOTS (default: the file SLOTFILE, default
# scripts/slots_prod.txt, re-read at each attempt) lists the slots this run may take. With MEMCHK_GB, waits after taking
# the slot until MemAvailable exceeds MEMCHK_GB (the box's mem_guard stops other jobs below 70 GB). Writes NAME.log, .err, .time.
set -u
D=${1:?}; N=${2:?}
case "$D" in ${NT_BOX}/work_parse_once/*) ;; *) echo "DIR must be under ${NT_BOX}/work_parse_once"; exit 2;; esac
cd "$D" || exit 2
W=${NT_BOX}/work_parse_once
TC=v4.34.0-rc2
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=1
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 RAYON_NUM_THREADS=1
PLP=$(cat $W/scripts/pkg_lean_path.txt)
export LEAN_PATH=${NT_BOX}/nt_fix7/$TC/.lake/build/lib/lean:${LIB:-$W/lib}:$D:$PLP
L=${NT_BOX}/elan/toolchains/leanprover--lean4---$TC/bin/lean
mkdir -p $W/slots
SLOT=
while [ -z "$SLOT" ]; do
  for i in ${SLOTS:-$(cat ${SLOTFILE:-$W/scripts/slots_prod.txt})}; do
    exec 9>$W/slots/slot$i
    if flock -n 9; then SLOT=$i; break; fi
    exec 9>&-
  done
  [ -z "$SLOT" ] && sleep 7
done
if [ -n "${MEMCHK_GB:-}" ]; then
  while [ "$(awk '/MemAvailable/ {print int($2/1048576)}' /proc/meminfo)" -lt "$MEMCHK_GB" ]; do sleep 20; done
fi
echo "$(date -u +%FT%TZ) slot=$SLOT start $D/$N mem=${MEMGB:-32} to=${TO:-7200}" >> $W/runs/lrun.log
: > "$N.err"
( ulimit -v $((${MEMGB:-32}*1024*1024)); ulimit -s unlimited
  /usr/bin/time -o "$N.time" -f "TIME %e s %M KB" timeout -k 30 ${TO:-7200} $L -j1 --tstack=1048576 ${OLEAN:+-o $N.olean} "$N.lean" > "$N.log" 2>> "$N.err"
  echo "rc=$?" >> "$N.log"; cat "$N.time" >> "$N.log" )
echo "$(date -u +%FT%TZ) slot=$SLOT end $D/$N $(tail -1 $N.log)" >> $W/runs/lrun.log
