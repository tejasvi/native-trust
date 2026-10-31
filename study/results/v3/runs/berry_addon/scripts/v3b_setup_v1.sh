#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3b_setup_v1.sh (v3 BerryEsseen on the clone): run as ntbuild inside a scope. Compiles the tokenizer add-on and BoCore
# (sources in $NT_BOX/v3/berry/src, the archived copies) against NativeTrust v15 into $NT_BOX/v3/berry/lib,
# as the P1 check did, and unpacks the 259 archived cover module sets (covers.tar) into covers/<tag>.
B=${NT_BOX}/v3/berry; TC=v4.34.0-rc2; L=${NT_BOX}/elan/toolchains/leanprover--lean4---$TC/bin/lean
NT=${NT_BOX}/nt_fix14/$TC/.lake/build/lib/lean; LPF=${NT_BOX}/work_bigcert/lp_34e448b1.txt
[ -s "$LPF" ] && [ -f "$NT/NativeTrust.olean" ] || { echo "missing NativeTrust build or LEAN_PATH cache"; exit 3; }
[ -e $B/lib ] && { echo "refusing: $B/lib exists"; exit 3; }
[ -e $B/covers ] && { echo "refusing: $B/covers exists"; exit 3; }
mkdir -p $B/lib $B/covers $B/logs || exit 3
export LEAN_PATH="$NT:$B/lib:$(cat $LPF)" ELAN_HOME=${NT_BOX}/elan LEAN_NUM_THREADS=1
for m in StrReplace SplitOnSpace StrRepl BeList BeObs BeSplitL BoCore; do
  ( cd $B/src && /usr/bin/time -f "maxrss_kb %M secs %e" $L -j1 --tstack=1048576 -o $B/lib/$m.olean $m.lean ) > $B/logs/lib_$m.log 2>&1
  rc=$?; echo "lib $m rc=$rc $(tail -1 $B/logs/lib_$m.log)"; [ $rc -eq 0 ] || exit $rc
done
tar -xf $B/covers.tar -C $B/covers || exit 4
echo "covers: $(ls $B/covers | wc -l) dirs, $(find $B/covers -name '*.lean' | wc -l) lean files"
