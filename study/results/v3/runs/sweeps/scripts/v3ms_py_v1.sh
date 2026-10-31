#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3ms_py_v1.sh SCRIPT [ARGS...]   -- run as ntbuild in a systemd unit v3ms-<x>-sweeps (paper v3, sweeps):
# python3 -I $NT_BOX/v3/sweeps/scripts/SCRIPT ARGS, output appended to $NT_BOX/v3/sweeps/logs/py.log.
M=${NT_BOX}/v3/sweeps; LOG=$M/logs/py.log
case "$1" in */*|'') echo "bad script $1" >> $LOG; exit 2;; esac
[ -f "$M/scripts/$1" ] || { echo "no script $1" >> $LOG; exit 2; }
echo "$(date -u +%FT%TZ) start $*" >> $LOG
python3 -I "$M/scripts/$@" >> $LOG 2>&1
echo "$(date -u +%FT%TZ) end $* rc=$?" >> $LOG
