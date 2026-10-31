#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3a_run_v1.sh (v3 components, R3 package add-ons): run as ntbuild inside a scope. The study driver copy with
# the final library and one add-on (oleans in $NT_BOX/v3/addons/ADDON) imported, on the facts that the v3 passes
# left unconverted (results v3u-NAME); run name v3a-ADDON-NAME; per fact 900 s and 48 GB, as the default run.
# usage: v3a_run_v1.sh NAME PKG ADDON JOBS MOD...
set -u
N=${1:?}; P=${2:?}; A=${3:?}; J=${4:?}; shift 4
case "$A" in *[!a-z0-9_]*) echo "bad add-on"; exit 2;; esac
AD=${NT_BOX}/v3/addons/$A
[ -d "$AD" ] && [ -s ${NT_BOX}/results/v3u-$N.ax.tsv ] || { echo "missing $AD or v3u-$N"; exit 3; }
imp=(); for m in "$@"; do [ -f "$AD/$m.olean" ] || { echo "missing $AD/$m.olean"; exit 3; }; imp+=(--extra-import "$m"); done
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=1
mkdir -p ${NT_BOX}/v3/opt/logs
LOG=${NT_BOX}/v3/opt/logs/v3a-$A-$N.out
echo "$(date -u +%FT%TZ) start v3a-$A-$N jobs=$J imports=$*" >> $LOG
python3 -u ${NT_BOX}/v3/m2_axioms5.py v3a-$A-$N "$P" --skip-build --nt-root ${NT_BOX}/nt_fix14 --jobs $J \
  --extra-path "$AD" "${imp[@]}" --from-results v3u-$N >> $LOG 2>&1
rc=$?
echo "$(date -u +%FT%TZ) end rc=$rc $(tail -1 $LOG)" >> $LOG
exit $rc
