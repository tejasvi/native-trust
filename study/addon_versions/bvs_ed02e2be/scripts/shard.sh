#!/usr/bin/env bash
# Usage: scripts/shard.sh PREP_FILE WORK_DIR [JOBS]
#
# Run from the root of a Lake package that depends on bvs (or of bvs itself), after `lake build` of the
# modules that PREP_FILE imports. Copies PREP_FILE into WORK_DIR and compiles it there; this runs the SAT
# solver and writes the shard files <P>_S<r>.lean and the final file <P>_Final.lean into WORK_DIR. Then
# compiles the shard files, JOBS at a time (default 4), and the final file. The converted theorems are in
# WORK_DIR/<P>_Final.olean; add WORK_DIR to LEAN_PATH to import <P>_Final.
set -euo pipefail
if [ $# -lt 2 ]; then
  echo "usage: $0 PREP_FILE WORK_DIR [JOBS]" >&2
  exit 2
fi
PREP=$1
WORK=$2
JOBS=${3:-4}
LP=$(lake env printenv LEAN_PATH)
LEAN=$(lake env sh -c 'command -v lean')
mkdir -p "$WORK"
P=$(basename "$PREP" .lean)
cp "$PREP" "$WORK/$P.lean"
cd "$WORK"
export LEAN_PATH="$PWD:$LP"
echo "prep: $P.lean"
"$LEAN" -o "$P.olean" "$P.lean"
echo "shards: $(ls "$P"_S*.lean | tr '\n' ' ')"
ls "$P"_S*.lean | sed 's/\.lean$//' | xargs -P "$JOBS" -I{} "$LEAN" -o {}.olean {}.lean
echo "final: ${P}_Final.lean"
"$LEAN" -o "${P}_Final.olean" "${P}_Final.lean"
