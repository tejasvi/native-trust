#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3oz_chain_v1.sh (v3 components, R2 for zcash): run as ntbuild inside one scope. (1) Options and controls on
# s_zcash_ironwood (v3pkg_chain_v1.sh on v3pkg_list_zcash.txt); (2) builds the shared staging module PrepZcash (v2's c22z
# source: four stage_native_axiom_nth commands with csimp, on the four fingerprint_matches facts, indices checked against
# v3's listax files) into $NT_BOX/v3/addons/zcash_prep with v3_addon_build_v2.sh (TO=3000 s, as v2's prep);
# (3) the zcash heavy case v3oz-s_zcash_ironwood (v3oh_run_v1.sh: combined options, 1,500 s as v2's batch, 48 GB,
# every check imports PrepZcash) on the facts that v3o-s_zcash_ironwood leaves. 3 facts at a time.
set -u
B=${NT_BOX}/v3/opt/bin
bash $B/v3pkg_chain_v1.sh $B/v3pkg_list_zcash.txt 3
TO=3000 bash $B/v3_addon_build_v2.sh zcash_prep v4.30.0 ${NT_BOX}/work_bigcert/lp_e2013183.txt PrepZcash || { echo "prep build failed"; exit 4; }
bash $B/v3oh_run_v1.sh v3oz s_zcash_ironwood ${NT_BOX}/repos_s/zcash_ironwood 1500 3 ${NT_BOX}/v3/addons/zcash_prep PrepZcash
echo "$(date -u +%FT%TZ) zcash chain end"
