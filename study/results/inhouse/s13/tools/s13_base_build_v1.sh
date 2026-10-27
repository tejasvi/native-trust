#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# s13_base_build_v1.sh (S(13) probe): run as ntbuild inside a systemd scope (MemoryMax). Builds the parts
# of the published S(13) >= 45 project (lean_s45 9f6aec78 in $NT_BOX/work_iterstr/s13/lean_s45, data files from the
# pinned local copies) that the probe imports: checker, data libraries, and the ct4 test slice. No chunk theorem.
# usage: s13_base_build_v1.sh LABEL JOBS TARGET...   (full log: $NT_BOX/work_iterstr/s13/logs/base_LABEL.log)
L=${1:?}; J=${2:?}; shift 2
P=${NT_BOX}/work_iterstr/s13/lean_s45; LOG=${NT_BOX}/work_iterstr/s13/logs/base_$L.log
case "$L" in *[!a-z0-9_]*) echo "bad label"; exit 2;; esac
[ -e "$LOG" ] && { echo "refusing: $LOG exists"; exit 3; }
mkdir -p ${NT_BOX}/work_iterstr/s13/logs && cd $P || exit 3
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=$J
ulimit -n 65536 2>/dev/null
echo "start $(date -u +%FT%TZ) jobs $J targets: $*" > $LOG
/usr/bin/time -f "maxrss_kb %M secs %e user %U sys %S" lake build "$@" >> $LOG 2>&1
rc=$?
echo "end $(date -u +%FT%TZ) rc=$rc" >> $LOG
tail -25 $LOG
exit $rc
