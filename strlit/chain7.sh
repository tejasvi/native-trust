#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# (as ntbuild on the box) wait for PID $1 (m6 chain) to end, then: maxRecDepth / stack-size variants of the repro (dir rd).
set -u
W=${1:?}
while kill -0 "$W" 2>/dev/null; do sleep 5; done
cd ${NT_BOX}/strlit || exit 2
mkdir -p rd
python3 -I gen4.py ${NT_BOX}/strlit/rd cnt:250:ubs:dk cnt:500:ubs:dk > /dev/null
for f in cnt_250_ubs_dk cnt_500_ubs_dk; do sed '/maxRecDepth/d' rd/$f.lean > rd/${f}_nomrd.lean; rm -f rd/$f.lean; done
sed '/maxRecDepth/d' repro/Repro.lean > rd/Repro_nomrd.lean
cp repro/Repro.lean rd/Repro_mrd.lean
TC=v4.34.0-rc2
echo "start (tstack 1GB, ulimit -s unlimited) $(date -u +%H:%M:%S)" >> rd/summary.$TC.tsv
./run2.sh $TC ${NT_BOX}/strlit/rd cnt_250_ubs_dk_nomrd cnt_500_ubs_dk_nomrd Repro_nomrd >> rd/summary.$TC.tsv
mkdir -p rd2; cp rd/Repro_nomrd.lean rd/Repro_mrd.lean rd2/
echo "start (default lean flags, default ulimit -s) $(date -u +%H:%M:%S)" >> rd2/summary.$TC.tsv
FLAGS=" " KEEPSTACK=1 ./run2.sh $TC ${NT_BOX}/strlit/rd2 Repro_nomrd Repro_mrd >> rd2/summary.$TC.tsv
echo "end $(date -u +%H:%M:%S)" >> rd2/summary.$TC.tsv
