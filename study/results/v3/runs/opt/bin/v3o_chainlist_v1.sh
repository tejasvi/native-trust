#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3o_chainlist_v1.sh (v3 components, R2): run as ntbuild inside one scope. Options (v3o_lane_v2.sh) on the packages of
# LIST (lines NAME PKG), then the single-option controls (v3oc_lane_v1.sh) on the same list; packages without unconverted
# facts or without conversions are skipped. JOBS facts at a time.
# usage: v3o_chainlist_v1.sh LIST JOBS
set -u
L=${1:?}; J=${2:?}
case "$J" in *[!0-9]*) echo "bad jobs"; exit 2;; esac
B=${NT_BOX}/v3/opt/bin
[ -s "$L" ] || { echo "missing $L"; exit 3; }
bash $B/v3o_lane_v2.sh "$L" "$J"
bash $B/v3oc_lane_v1.sh "$L" "$J"
echo "$(date -u +%FT%TZ) chain $L end"
