#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# s13_probe_v1.sh (S(13) probe): run as root (sudo), under coreh_guard_v2 --run. Runs the probe files
# ID... of DIR, at most PAR at a time, each in its own systemd scope as ntbuild with MemoryMax=MEMG (no swap) and the
# wall-clock limit T. Before the batch: MemAvailable >= 64 GB + PAR x MEMG; before each fact: >= 64 GB + MEMG (waits).
# usage: s13_probe_v1.sh DIR T MEMG PAR ID...
D=${1:?}; T=${2:?}; MEMG=${3:?}; PAR=${4:?}; shift 4
R=${NT_BOX}/work_iterstr/s13/bin/s13_fact_v1.sh
avail=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo)
if [ "$avail" -lt $((64 + PAR * MEMG)) ]; then echo "NOT STARTED: MemAvailable $avail GB < $((64 + PAR * MEMG)) GB"; exit 4; fi
echo "$(date -u +%FT%TZ) batch: ${#} facts, PAR=$PAR MEMG=$MEMG T=$T MemAvailable=${avail}G"
one() {
  local id=$1 a
  while :; do a=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo); [ "$a" -ge $((64 + MEMG)) ] && break
    echo "$(date -u +%FT%TZ) wait $id MemAvailable=${a}G"; sleep 30; done
  local unit=s13-f-$(echo $id | tr '_' '-' | tr 'A-Z' 'a-z')-$(date +%s)
  echo "$(date -u +%FT%TZ) start $id unit=$unit MemAvailable=${a}G"
  systemd-run --scope --quiet --unit=$unit -p MemoryMax=${MEMG}G -p MemorySwapMax=0 --uid=ntbuild --gid=ntbuild bash $R $D $id $T
  local rc=$?
  echo "$(date -u +%FT%TZ) end $id rc=$rc | $(tail -2 $D/$id.log | head -1 | cut -c1-120) | $(tail -1 $D/$id.log)"
}
for id in "$@"; do
  while [ "$(jobs -rp | wc -l)" -ge "$PAR" ]; do sleep 5; done
  one $id &
  sleep 2
done
wait
echo "$(date -u +%FT%TZ) batch done"
