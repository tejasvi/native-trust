#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# usage (as ntbuild on the box): batch.sh TC DIR SPEC...   -- gen4.py the specs into DIR, then run.sh them (4 at once);
# summary lines appended to DIR/summary.TC.tsv
set -u
TC=${1:?}; DIR=${2:?}; shift 2
case "$DIR" in ${NT_BOX}/strlit/*) ;; *) echo "DIR must be under ${NT_BOX}/strlit"; exit 2;; esac
cd ${NT_BOX}/strlit || exit 2
NAMES=$(python3 -I gen4.py "$DIR" "$@" | awk '{print $1}')
echo "start $(date -u +%H:%M:%S)" >> "$DIR/summary.$TC.tsv"
./run.sh "$TC" "$DIR" $NAMES >> "$DIR/summary.$TC.tsv"
echo "end $(date -u +%H:%M:%S)" >> "$DIR/summary.$TC.tsv"
