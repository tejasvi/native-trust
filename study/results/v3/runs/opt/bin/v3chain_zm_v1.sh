#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3chain_zm_v1.sh (v3 components): run as ntbuild inside one scope: the zcash chain (v3oz_chain_v1.sh:
# options, controls, PrepZcash, v3oz), then minidregg (v3pkg_chain_v1.sh on v3pkg_list_md.txt: options, controls, the
# add-on NTMinidreggC4 as v3a-minidregg-s_emberian_minidregg), 3 facts at a time.
set -u
B=${NT_BOX}/v3/opt/bin
bash $B/v3oz_chain_v1.sh
bash $B/v3pkg_chain_v1.sh $B/v3pkg_list_md.txt 3
echo "$(date -u +%FT%TZ) chain zm end"
