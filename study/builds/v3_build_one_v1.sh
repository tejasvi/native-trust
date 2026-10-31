#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3_build_one_v1.sh (2026-10-29): nt_fix14_build_one.sh with the build root $NT_BOX/v3/nt_v15, for toolchains
# that $NT_BOX/nt_fix14 lacks (v4.28.0). Same sources (SRC = $NT_BOX/nt_fix14/src), same body.
# systemd scope that carries the memory cap (MemoryMax), so no ulimit here. Body as in nt_fix13_build.sh.
# usage: v15_build_one.sh SRC W TC
SRC=${1:?}; W=${2:?}; tc=${3:?}
case "$W" in ${NT_BOX}/v3/nt_v15) ;; *) echo "bad W $W"; exit 2;; esac
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=2
d=$W/$tc
case "$d" in "$W"/v4.*|"$W"/nightly-*) ;; *) echo "bad dir $d"; exit 2;; esac
[ -e "$d" ] && { echo "$tc REFUSED: $d exists"; exit 3; }
mkdir -p "$d/NativeTrust/Driver"
cp $SRC/lakefile.toml $SRC/NativeTrust.lean "$d/"; cp $SRC/NativeTrust/*.lean "$d/NativeTrust/"; cp $SRC/NativeTrust/Driver/*.lean "$d/NativeTrust/Driver/"
case $tc in v4.27*|v4.28*|v4.29*) cp $SRC/NativeTrust/CSimpCompatStub.lean.txt "$d/NativeTrust/CSimpCompat.lean"; cp $SRC/NativeTrust/StrLibStub.lean.txt "$d/NativeTrust/StrLib.lean";; esac
echo "leanprover/lean4:$tc" > "$d/lean-toolchain"
cd "$d" && ( timeout 2400 lake build NativeTrust NativeTrust.KernelFirst NativeTrust.KernelFirstLite ntrust > build.log 2>&1; echo "exit $?" >> build.log )
if grep -q '^exit 0' build.log; then r="$tc OK $(date -u +%T)"; else r="$tc FAIL: $(grep -m5 'error' build.log | cut -c1-300 | tr '\n' ' ')"; fi
echo "$r" > $W/result_$tc.txt; echo "$r"
