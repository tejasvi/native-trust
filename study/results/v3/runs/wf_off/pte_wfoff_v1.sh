NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# pte_wfoff_v1.sh -- sent to `bash -s` as ntbuild on the study machine (2026-10-30): rs-mca's
# MomentToMax.PTEClusterPacking.champion_packingStats (theorem 1 of #native_theorems) checked again with the final library build of
# the heavy pass (v3/nt_v15/v4.28.0) WITHOUT the well-founded replacement (wf := false), with the command of the baseline run's
# ablation (study/results/ablation/rs-mca-moment_to_max/chk4_wfoff.lean). One process, input on stdin (lean --stdin, through a
# pipe), nothing written on the machine; address space 60 GiB, 25 minutes wall (timeout kills the process group).
set -u
P=${NT_BOX}/repos/rs-mca/experimental/lean/moment_to_max
NT=${NT_BOX}/v3/nt_v15/v4.28.0
L=${NT_BOX}/elan/toolchains/leanprover--lean4---v4.28.0/bin/lean
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=1
LP=$NT/.lake/build/lib/lean:$P/.lake/build/lib/lean
for d in $(ls -d $P/.lake/packages/*/.lake/build/lib/lean | LC_ALL=C sort); do LP=$LP:$d; done
export LEAN_PATH=$LP
cd $P || exit 2
echo "start $(date -u +%FT%TZ) host_cores=$(nproc) LEAN_PATH=$LEAN_PATH"
s=$(date +%s)
printf '%s\n' 'import NativeTrust' 'import MomentToMax.PTEClusterPacking' 'set_option Elab.async false' 'set_option maxHeartbeats 0' \
  'set_option maxRecDepth 1000000' 'set_option nativeTrust.eprint true' '#kernel_blockers_nth MomentToMax.PTEClusterPacking 1' \
  'trust_check_nth MomentToMax.PTEClusterPacking 1 (config := { split := 8, wf := false, trace := true })' \
  | ( ulimit -n 65536 2>/dev/null || ulimit -n $(ulimit -Hn); ulimit -v 62914560
      exec timeout -k 30 1500 /usr/bin/time -f "maxrss_kb %M" $L -j1 --tstack=1048576 --stdin ) 2>&1
echo "rc=$? secs=$(( $(date +%s) - s )) end $(date -u +%FT%TZ)"
