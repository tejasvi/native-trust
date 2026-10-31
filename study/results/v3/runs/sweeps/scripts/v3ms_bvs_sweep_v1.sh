#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3ms_bvs_sweep_v1.sh STEP...   -- run as ntbuild in a systemd unit v3ms-bvs<k>-sweeps (paper v3, sweeps).
# Runs the steps of bvs_v3.py in order, each as `python3 -I bvs_v3.py <step words>`; a step is one argument with
# its words separated by ':' (for example list:--jobs:2  run:p1:--jobs:2:--budget-gb:8:--max-pred:8  check:p1).
# Stops at the first step that fails. Log: $NT_BOX/v3/sweeps/logs/bvs_sweep.log
M=${NT_BOX}/v3/sweeps; LOG=$M/logs/bvs_sweep.log
cd $M/bvs || exit 2
for s in "$@"; do
  IFS=: read -r -a w <<< "$s"
  echo "$(date -u +%FT%TZ) step start ${w[*]}" >> $LOG
  python3 -I $M/scripts/bvs_v3.py "${w[@]}" >> $LOG 2>&1
  rc=$?
  echo "$(date -u +%FT%TZ) step end ${w[*]} rc=$rc" >> $LOG
  [ $rc -eq 0 ] || exit $rc
done
