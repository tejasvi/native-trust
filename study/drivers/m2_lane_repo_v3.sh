#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3 lane runner (2026-10-29): per-theorem lanes (Lean 4.28 rs-mca sub-projects): runs the artifact's driver copy
# $NT_BOX/v3/m2_repo4.py and writes outputs under $NT_BOX/v3. Run as ntbuild (systemd unit).
# usage: m2_lane_v3.sh LANE_FILE LOG [driver args...]   (LANE_FILE lines: NAME<TAB>PKG<TAB>EXTRA_ARGS)
LANE=$1; LOG=$2; shift 2
V3=${NT_BOX}/v3
mkdir -p $V3/out
{
  echo "$(date -u +%FT%TZ) lane start $LANE args: $*"
  while IFS=$'\t' read -r name pkg extra; do
    [ -n "$name" ] || continue
    echo "$(date -u +%FT%TZ) start $name $extra"
    # shellcheck disable=SC2086
    python3 -u $V3/m2_repo4.py "$name" "$pkg" $extra "$@" > $V3/out/m2_$name.repo4.out 2>&1
    rc=$?
    echo "$(date -u +%FT%TZ) end $name rc=$rc $(tail -1 $V3/out/m2_$name.repo4.out)"
  done < "$LANE"
  echo "$(date -u +%FT%TZ) lane end $LANE"
} >> "$LOG" 2>&1
