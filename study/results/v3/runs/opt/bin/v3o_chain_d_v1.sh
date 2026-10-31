#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3o_chain_d_v1.sh (v3 components, R2): run as ntbuild inside one scope, after chain c. Options lane d
# (v3o_list_d.txt: sample packages final after 10:00Z), then the single-option controls on the same list (packages
# without conversions are skipped), 3 facts at a time.
set -u
B=${NT_BOX}/v3/opt/bin
bash $B/v3o_lane_v2.sh $B/v3o_list_d.txt 3
bash $B/v3oc_lane_v1.sh $B/v3o_list_d.txt 3
echo "$(date -u +%FT%TZ) chain d end"
