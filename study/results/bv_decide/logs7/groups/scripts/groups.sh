#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# On the box as ntbuild: groups.sh -- B08 groups: compile groups/GMemory.lean (veir, v4.35.0-rc4) and groups/GNatuvea.lean
# (tacenta model + proofs, v4.31.0) with build10, then the fresh-process acceptance checks with nanoda on every fact
# theorem and rebuilt declaration of each group.
set -u
W=${NT_BOX}/work_bvscale
cd $W
source scripts/paths.sh
for g in GMemory:v4.35.0-rc4:VEIR_PATH:Veir.Interpreter.Memory GNatuvea:v4.31.0:NATUVEA_PATH:Proofs.Serialization; do
  IFS=: read -r G TC XPV ORIG <<< "$g"
  t0=$(date -u +%T)
  BV_BUILD=build10 BV_EXTRA_PATH=${!XPV} BV_TIMEOUT=3600 ./scripts/run.sh $TC groups $G.lean $G > logs/g_$G.log 2>&1
  echo "$G rc=$? start=$t0 end=$(date -u +%T) $(grep TIME logs/g_$G.log)" >> logs/groups.log
  DECLS="$(awk -F'\t' '$1=="BVS_UNSAT" {print $9}' logs/g_$G.log | tr '\n' ' ') $(awk -F'\t' '$1=="BVS_USER" {print $3}' logs/g_$G.log | tr '\n' ' ')"
  XP=$XPV BV_BUILD=build10 ./scripts/accept.sh $TC $G $G $ORIG @$W/logs/g_$G.log @$W/logs/g_$G.log $DECLS > logs/accept_$G.log 2>&1
  echo "$G accept done $(date -u +%T): $(grep -E 'nanoda (PASS|FAIL)' logs/accept_$G.log | cut -c1-120)" >> logs/groups.log
done
