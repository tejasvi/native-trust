#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3ms_bvsH_v1.sh   -- run as ntbuild in the systemd unit v3ms-bvsH-sweeps (50G; paper v3, sweeps): the heavy part
# of the v3 bv_decide sweep, in order:
#  1. the facts of run p1 that the 9G pass left (predicted above 8 GB), one process at a time, 900 s / 48 GiB, as the
#     study's sweep (bvs_v3.py run p1 --jobs 1 --budget-gb 48 --max-pred 48);
#  2. the fresh-process checks of every CONVERTED fact of p1 (bvs_v3.py check p1; rewrites checks/p1.axioms.tsv);
#  3. the study's follow-ups for the p1 facts that end TIMEOUT (bvs5_prep, 4 shards) or MEMORY / ERROR killed
#     (bvs6_prep, segments of 30,000 gates, 4 shards), shards 2 at a time (bvs_v3_pass2.py shard);
#  4. the two groups of the study (bvs_v3_pass2.py group): GMemory = Veir.Interpreter.Memory facts 0 and 1 (veir),
#     GNatuvea = Model.CompositeHeader facts 0 and 1 with Proofs.Serialization fact 0 (tacenta-proofs).
# Log: $NT_BOX/v3/sweeps/logs/bvs_sweep.log
M=${NT_BOX}/v3/sweeps; LOG=$M/logs/bvs_sweep.log; S=$M/scripts
cd $M/bvs || exit 2
step() { echo "$(date -u +%FT%TZ) H step start $*" >> $LOG; python3 -I "$@" >> $LOG 2>&1; rc=$?; echo "$(date -u +%FT%TZ) H step end $* rc=$rc" >> $LOG; return $rc; }
step $S/bvs_v3.py run p1 --jobs 1 --budget-gb 48 --max-pred 48 || exit 3
step $S/bvs_v3.py check p1 --jobs 2
# follow-ups: last row per fact of p1
awk -F'\t' 'NR > 1 {last[$2 "\t" $3 "\t" $4] = $6 "\t" $7} END {for (k in last) print k "\t" last[k]}' results/p1.tsv | sort |
while IFS=$'\t' read -r pkg mod idx verdict reason; do
  case "$verdict" in
    TIMEOUT) mode=shards;;
    MEMORY) mode=split;;
    ERROR) case "$reason" in killed*) mode=split;; *) continue;; esac;;
    *) continue;;
  esac
  name=$(echo "${mod}_${idx}" | tr -c 'A-Za-z0-9\n' 'x' | tail -c 60)
  step $S/bvs_v3_pass2.py shard "S$name" "$pkg" "$mod" "$idx" $mode --par 2 < /dev/null
done
step $S/bvs_v3_pass2.py group GMemory s_opencompl_veir "Veir.Interpreter.Memory:0,1"
step $S/bvs_v3_pass2.py group GNatuvea s_Natuvea_tacenta_core_tacenta_proofs "Model.CompositeHeader:0,1" "Proofs.Serialization:0"
echo "$(date -u +%FT%TZ) H all done" >> $LOG
