#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# (as ntbuild on the box) wait for the m4 batch (PID given) to end, then: repro files on both toolchains, then batch m5.
set -u
W=${1:?}
while kill -0 "$W" 2>/dev/null; do sleep 5; done
cd ${NT_BOX}/strlit || exit 2
for TC in v4.34.0-rc2 v4.35.0; do
  echo "start $(date -u +%H:%M:%S)" >> repro/summary.$TC.tsv
  ./run.sh $TC ${NT_BOX}/strlit/repro Repro ReproControl ReproArray >> repro/summary.$TC.tsv
done
./batch3.sh v4.34.0-rc2 ${NT_BOX}/strlit/m5 dw:4000:ubs:dk cnt:2000:ubs:dk dw:1000:len:dk rep8:1000:u8push:dk B-01234567:8000:ubs:dk B-613/201_:8000:ubs:dk B-613/2000:8000:ubs:dk B-613/200_:8000:ubs:dk B-613/200_:7000:ubs:dk
