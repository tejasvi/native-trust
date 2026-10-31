#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3a_chain_v1.sh (v3 components, R3 package add-ons and the csimp add-on): run as ntbuild inside one scope.
# Writes the unconverted list v3u-NAME if it is missing (v3u_list_v1.sh), then runs v3a_run_v2.sh for each
# ADDON:MOD[,MOD...] in turn (run name v3a-ADDON-NAME, per fact 900 s and 48 GB), JOBS facts at a time.
# usage: v3a_chain_v1.sh NAME PKG JOBS ADDON:MODS...
set -u
N=${1:?}; P=${2:?}; J=${3:?}; shift 3
case "$N" in *[!A-Za-z0-9_.-]*) echo "bad name"; exit 2;; esac
case "$J" in *[!0-9]*) echo "bad jobs"; exit 2;; esac
B=${NT_BOX}/v3/opt/bin; R=${NT_BOX}/results
[ -d "$P" ] || { echo "no dir $P"; exit 3; }
[ -e "$R/v3u-$N.ax.tsv" ] || bash $B/v3u_list_v1.sh "$N" || exit 3
for spec in "$@"; do
  a=${spec%%:*}; mods=${spec#*:}
  case "$a" in ''|*[!a-z0-9_]*) echo "bad add-on $a"; continue;; esac
  echo "$(date -u +%FT%TZ) chain: start v3a-$a-$N ($(wc -l < $R/v3u-$N.ax.tsv) facts, modules ${mods//,/ })"
  bash $B/v3a_run_v2.sh "$N" "$P" "$a" "$J" ${mods//,/ }
  echo "$(date -u +%FT%TZ) chain: end v3a-$a-$N rc=$?"
done
