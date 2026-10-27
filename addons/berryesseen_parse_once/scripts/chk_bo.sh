#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# usage (as ntbuild on the box): [SLOTS=2] [LIB=...] chk_bo.sh DIR MODULE THM...
# Export THM... (with their closure) from DIR/MODULE.olean with lean4export (v4.34.0-rc2), then check the export with
# nanoda and con-ron (bundled with v4.35.0), permitted axioms propext, Classical.choice, Quot.sound (configuration of
# the strings add-on's checks). Holds one slot lock (work_parse_once/slots) while running. Writes DIR/MODULE.{export,nanoda.*,conron.txt,chk}.
set -u
D=${1:?}; M=${2:?}; shift 2; THMS="$*"
case "$D" in ${NT_BOX}/work_parse_once/*) ;; *) echo "DIR must be under ${NT_BOX}/work_parse_once"; exit 2;; esac
cd "$D" || exit 2
W=${NT_BOX}/work_parse_once
TC=v4.34.0-rc2
EXP=${NT_BOX}/strrepl/lean4export-v4.34.0-rc2/.lake/build/bin/lean4export
CHK=${NT_BOX}/elan/toolchains/leanprover--lean4---v4.35.0/bin
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/toolchains/leanprover--lean4---$TC/bin:${NT_BOX}/elan/bin:$PATH
export LEAN_PATH=${NT_BOX}/nt_fix7/$TC/.lake/build/lib/lean:${LIB:-$W/lib3}:$D:$(cat $W/scripts/pkg_lean_path.txt)
SLOT=
while [ -z "$SLOT" ]; do
  for i in ${SLOTS:-$(cat $W/scripts/slots_prod.txt)}; do
    exec 9>$W/slots/slot$i
    if flock -n 9; then SLOT=$i; break; fi
    exec 9>&-
  done
  [ -z "$SLOT" ] && sleep 7
done
echo "$(date -u +%FT%TZ) slot=$SLOT start chk $D/$M" >> $W/runs/lrun.log
ulimit -s unlimited
( ulimit -v $((${MEMGB:-48}*1024*1024)); timeout 7200 "$EXP" "$M" -- $THMS > "$M.export" 2> "$M.export.err" ); erc=$?
ulimit -v $((${CHKMEM:-120}*1024*1024))
cat > "$M.nanoda.json" <<J
{"export_file_path": "$D/$M.export", "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
 "unpermitted_axiom_hard_error": true, "nat_extension": true, "string_extension": true, "print_success_message": true, "num_threads": 1}
J
/usr/bin/time -f "nanoda: %e s %M KB" timeout ${CHKTO:-14400} $CHK/nanoda_bin "$M.nanoda.json" > "$M.nanoda.txt" 2>&1; nrc=$?
if [ -z "${NOCONRON:-}" ]; then /usr/bin/time -f "con-ron: %e s %M KB" timeout ${CHKTO:-14400} $CHK/con-ron "$M.export" > "$M.conron.txt" 2>&1; crc=$?; else echo "con-ron: skipped" > "$M.conron.txt"; crc=skipped; fi
N=$(grep -o 'Checked [0-9]* declarations with no typechecker errors' "$M.nanoda.txt")
C=$(grep -o 'accepted [0-9]* declarations' "$M.conron.txt"); CD=$(grep -o 'con-ron: declined: .*' "$M.conron.txt" | head -1)
echo "$M thms=[$THMS] export_rc=$erc lines=$(wc -l < $M.export) nanoda_rc=$nrc [$N] conron_rc=$crc [$C] $CD $(tail -1 $M.nanoda.txt) $(tail -1 $M.conron.txt)" | tee "$M.chk"
echo "$(date -u +%FT%TZ) slot=$SLOT end chk $D/$M nanoda_rc=$nrc conron_rc=$crc" >> $W/runs/lrun.log
