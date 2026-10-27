#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# (as ntbuild on the box) full DW21 literal (7,824 chars), self-contained, with and without maxRecDepth (dir full).
set -u
cd ${NT_BOX}/strlit || exit 2
mkdir -p full
python3 -I gen4.py ${NT_BOX}/strlit/full dw:7824:ubs:dk > /dev/null
sed '/maxRecDepth/d' full/dw_7824_ubs_dk.lean > full/dw_7824_ubs_dk_nomrd.lean
TC=v4.34.0-rc2
echo "start $(date -u +%H:%M:%S)" >> full/summary.$TC.tsv
./run2.sh $TC ${NT_BOX}/strlit/full dw_7824_ubs_dk dw_7824_ubs_dk_nomrd >> full/summary.$TC.tsv
FLAGS=" " KEEPSTACK=1 ./run2.sh $TC ${NT_BOX}/strlit/full dw_7824_ubs_dk_nomrd > /dev/null
mv full/dw_7824_ubs_dk_nomrd.$TC.log full/dw_7824_ubs_dk_nomrd.defaultflags.$TC.log
printf 'dw_7824_ubs_dk_nomrd (default lean flags + default ulimit -s)\t%s\t%s\n' "$(grep -o 'TIME.*' full/dw_7824_ubs_dk_nomrd.defaultflags.$TC.log | tail -1)" "$(tail -1 full/dw_7824_ubs_dk_nomrd.defaultflags.$TC.log)" >> full/summary.$TC.tsv
echo "end $(date -u +%H:%M:%S)" >> full/summary.$TC.tsv
