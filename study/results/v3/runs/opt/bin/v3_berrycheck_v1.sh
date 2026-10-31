#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3_berrycheck_v1.sh (v3, BerryEsseen feasibility): run as ntbuild inside a systemd scope (MemoryMax). Compiles the
# BerryEsseen tokenizer add-on modules and the parse-once core (archived copies in SRC) against NativeTrust v15
# ($NT_BOX/nt_fix14/v4.34.0-rc2) and BerryEsseen's search path, one module at a time, unchanged.
# usage: v3_berrycheck_v1.sh
B=${NT_BOX}/v3/berry_check; SRC=$B/src; LIB=$B/lib; LOGD=$B/logs
TC=v4.34.0-rc2; L=${NT_BOX}/elan/toolchains/leanprover--lean4---$TC/bin/lean
NT=${NT_BOX}/nt_fix14/$TC/.lake/build/lib/lean
LPF=${NT_BOX}/work_bigcert/lp_34e448b1.txt
[ -s "$LPF" ] || { echo "no LEAN_PATH cache $LPF"; exit 3; }
[ -f "$NT/NativeTrust.olean" ] || { echo "no NativeTrust build $NT"; exit 3; }
mkdir -p $LIB $LOGD || exit 3
export LEAN_PATH="$NT:$LIB:$(cat $LPF)" ELAN_HOME=${NT_BOX}/elan LEAN_NUM_THREADS=1
echo "start $(date -u +%FT%TZ) nt=$NT"
for m in StrReplace SplitOnSpace StrRepl BeList BeObs BeSplitL BoCore; do
  [ -e "$LOGD/$m.log" ] && { echo "refusing: $LOGD/$m.log exists"; exit 3; }
  ( cd $SRC && /usr/bin/time -f "maxrss_kb %M secs %e" $L -j1 --tstack=1048576 -o $LIB/$m.olean $m.lean ) > $LOGD/$m.log 2>&1
  rc=$?
  echo "$m rc=$rc $(tail -1 $LOGD/$m.log) errors=$(command grep -c 'error' $LOGD/$m.log)"
done
echo "end $(date -u +%FT%TZ)"
