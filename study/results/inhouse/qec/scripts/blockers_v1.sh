#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# task 3: static blocker report (`#kernel_blockers T`, NativeTrust v15: nothing is evaluated, no copy built) for
# every QEC theorem with native facts, one lean process per theorem module, in parallel (9 modules). Output
# qec/blockers/Blk_<module>.{lean,log}. Runs as ntbuild inside a systemd unit (MemoryMax); no ulimit -v.
set -u
Q=${NT_BOX}/work_resv8/qec; O=$Q/blockers
B=${NT_BOX}/elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin
export ELAN_HOME=${NT_BOX}/elan PATH=$B:${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=1
mkdir -p "$O" && cd "$O" || exit 2
LP=$(cd "$Q/lean4" && lake env printenv LEAN_PATH) || exit 2
export LEAN_PATH=${NT_BOX}/nt_fix14/v4.35.0-rc3/.lake/build/lib/lean:$LP
one() {  # MODULE THEOREM...
  m=$1; shift; f=Blk_$(echo "$m" | tr . _)
  { echo "import NativeTrust"; echo "import $m"; echo "set_option maxHeartbeats 0"
    for t in "$@"; do echo "#kernel_blockers $t"; done; } > "$f.lean"
  /usr/bin/time -f "blockers: %e s wall %U s user %M KB" timeout 3600 "$B/lean" -j1 --tstack=1048576 "$f.lean" > "$f.log" 2>&1
  echo "rc=$?" >> "$f.log"
}
one QEC.ChecksN.Thm11V2 QEC.Circ.thm11_circuit_native &
one QEC.ChecksN8.Thm12V2 QEC.Circ.thm12_circuit_native &
one QEC.ChecksNS.Thm12bV2 QEC.Circ.thm12b_circuit_native &
one QEC.ChecksNW.Thm13aV2 QEC.Circ.thm13a_lean_native &
one QEC.ChecksNW.Thm13bV2 QEC.Circ.thm13b_native QEC.Circ.thm13b_lean_native &
one QEC.ChecksNS.Thm13cV2 QEC.Circ.thm13c_native QEC.Circ.thm13c_lean_native &
one QEC.ChecksNW.Thm81aV2 QEC.Circ.thm81a_helios_native QEC.Circ.thm81a_h2_native &
one QEC.ChecksNW.Thm81bV2 QEC.Circ.thm81b_heron_native QEC.Circ.thm81b_helios_native QEC.Circ.thm81b_h2_native &
one QEC.ChecksNS.Thm81cV2 QEC.Circ.thm81c_heron_native QEC.Circ.thm81c_helios_native QEC.Circ.thm81c_h2_native &
wait
echo "$(date -u +%FT%TZ) blockers done" > "$O/done.txt"
