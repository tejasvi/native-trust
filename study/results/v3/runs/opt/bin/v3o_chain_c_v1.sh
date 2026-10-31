#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3o_chain_c_v1.sh (v3 components, R2): run as ntbuild inside one scope, after options lane b. Options lane c
# (v3o_list_c.txt: aks), then the single-option controls (v3oc_lane_v1.sh on v3oc_list_v1.txt; packages without
# conversions are skipped), then the TrainVerify heavy case (v3oh-trainverify, 3,000 s), each 3 facts at a time.
set -u
B=${NT_BOX}/v3/opt/bin
bash $B/v3o_lane_v2.sh $B/v3o_list_c.txt 3
bash $B/v3oc_lane_v1.sh $B/v3oc_list_v1.txt 3
bash $B/v3oh_run_v1.sh v3oh trainverify ${NT_BOX}/repos/tainverify_lean/trainverify 3000 3
echo "$(date -u +%FT%TZ) chain c end"
