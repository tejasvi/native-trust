#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3_build_many_v1.sh (2026-10-29): build the final library (nt_fix14/src) for each toolchain given, one after the
# other, with v3_build_one_v1.sh into $NT_BOX/v3/nt_v15 (it refuses existing dirs). Run as ntbuild in a unit.
# usage: v3_build_many_v1.sh TC...
for tc in "$@"; do
  bash ${NT_BOX}/v3/v3_build_one_v1.sh ${NT_BOX}/nt_fix14/src ${NT_BOX}/v3/nt_v15 "$tc"
done
