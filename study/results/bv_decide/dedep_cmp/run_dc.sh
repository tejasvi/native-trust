#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# On the box as ntbuild: run_dc.sh W...  -- one width at a time (whole file, LEAN_NUM_THREADS=1, 40 GiB address space)
set -u
W=${NT_BOX}/work_bvscale
cd $W
for w in "$@"; do
  echo "== w=$w start $(date -u +%T)" >> $W/logs/DC_runs.log
  BV_BUILD=build7 BV_VMEM_KB=41943040 BV_TIMEOUT=3600 ./scripts/run.sh v4.33.1 bench/dedep_cmp DC_w$w.lean > $W/logs/DC_w$w.log 2>&1
  rc=$?
  echo "== w=$w end $(date -u +%T) rc=$rc" >> $W/logs/DC_runs.log
done
