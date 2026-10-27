#!/bin/bash
# s13_scoped.sh (S(13) probe): run as root (sudo), under coreh_guard_v2 --run. Starts one command as
# ntbuild in its own systemd scope with MemoryMax=MEMG (no swap), after checking MemAvailable >= 64 GB + MEMG (the box
# is shared with the QEC runs).
# usage: s13_scoped.sh NAME MEMG CMD ARGS...
NAME=${1:?}; MEMG=${2:?}; shift 2
avail=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo)
if [ "$avail" -lt $((64 + MEMG)) ]; then echo "$NAME NOT STARTED: MemAvailable $avail GB < $((64 + MEMG)) GB"; exit 4; fi
unit=s13-$NAME-$(date +%s)
echo "$(date -u +%FT%TZ) start unit=$unit MemoryMax=${MEMG}G MemAvailable=${avail}G"
systemd-run --scope --quiet --unit=$unit -p MemoryMax=${MEMG}G -p MemorySwapMax=0 --uid=ntbuild --gid=ntbuild "$@"
rc=$?
echo "$(date -u +%FT%TZ) end unit=$unit rc=$rc"
exit $rc
