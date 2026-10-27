# Theorem 1.1 on the box: native and kernel-only builds, and the hand-built part

- Tree and toolchain: the v2 tree (export of commit 643d947) and Lean v4.35.0-rc3, on the same box as the NativeTrust
  run.
- Settings: those of the project scripts run_checks.sh and run_final.sh, that is one lean process per module,
  LEAN_NUM_THREADS=1, nice 10 and the same -D options.
- Kernel-only version: the 34 per-outcome chunks F_[ZX]_13_* first, 12 at once, then the other 356 check modules 24 at
  once, then AllK and Thm11V3.
- Native version: the 10 check modules N_* 24 at once, then AllN and Thm11V2.
- Sources were copied from the tree, and outputs went to a fresh root that comes first on LEAN_PATH. The library's QEC
  oleans were copied into it and checked against the existing build (logs/libcopy.sum). Mathlib and the other packages
  were read from the existing build.
- CPU: the unit cgroup cpu.stat between the phase marks (logs/phases.log), GNU time per module (t11_modules.tsv), and a
  core-hour guard with a 6 core-h cap. The guard log (logs/guard.log) shows 1.685 core-h for the whole unit.
- The first attempt (attempt1/) failed in 5 s. Lean resolves every QEC.* module under the first LEAN_PATH root that has
  a QEC directory, and the fresh root held only the outputs. The second attempt copies the library oleans in first.
- The dependencies, the QEC library modules that these modules import, were already built by `lake build QEC QECComp`
  for the whole library (275 CPU-s, build/setup.log). They are not counted here.
- Both theorems print their axioms. The kernel-only theorem depends on propext, Classical.choice and Quot.sound
  (logs/out_QEC_Checks_Thm11V3.txt), and the native one on the same three plus 61 native_decide axioms
  (logs/out_QEC_ChecksN_Thm11V2.txt).

## Results (t11_summary.tsv)

```
part	modules	ok	cgroup_cpu_s	sum_user_sys_s	max_module_wall_s	max_rss_gib	phase_start	phase_end
kernel_check	390	390	5780.8	5773.8	51.4	12.81	2026-10-26T07:25:12Z	2026-10-26T07:30:35Z
kernel_final	2	2	27.8	27.8	6.2	3.89	2026-10-26T07:30:35Z	2026-10-26T07:30:42Z
native_check	10	10	253.5	253.3	59.9	3.31	2026-10-26T07:30:42Z	2026-10-26T07:31:42Z
native_final	2	2	2.7	2.6	1.3	3.32	2026-10-26T07:31:42Z	2026-10-26T07:31:45Z

kernel-only version (390 check modules + AllK + Thm11V3): cgroup CPU 5808.7 s = 1.614 core-h, wall 2026-10-26T07:25:12Z to 2026-10-26T07:30:42Z
native version (10 N_* modules + AllN + Thm11V2): cgroup CPU 256.2 s = 0.0712 core-h, wall 2026-10-26T07:30:42Z to 2026-10-26T07:31:45Z
parallelism: one lean process per module, LEAN_NUM_THREADS=1, nice 10; 24 at once (the F_[ZX]_13 chunks 12 at once)
```

## Hand-written and generated Lean (counts/, script scripts/count_t11_v2.py)

The rule in both trees' FORMALIZATION.md (line 3) counts as hand-written the .lean files under QEC/ and QECComp/ (in v3
also QECKernel/) and the root modules QEC.lean and QECComp.lean. It leaves out the generated data modules
(QECComp/Data), the check directories QEC/Checks* and, in v3, the generated kernel modules: the subdirectories of
QECKernel/ other than Fin/, and QECKernel/AggTab.lean. Lines are counted with wc -l. The working trees were checked to
equal the release commits for every .lean file and generator (git status, git diff 9a639b4). The counts
(counts/counts.txt):

```
v2: hand-written 89 files / 18643 lines; excluded as generated 1019 files
v3: hand-written 128 files / 25091 lines; excluded as generated 5757 files
v3 kernel part: hand-written QECKernel files 39 / 6448 lines (top level 31, Fin/ 8); generated QECKernel files 4738; v2 rule part in v3: 89 / 18643 lines
v3 kernel generators: gen/kernel/mkcov3.py 104, gen/kernel/mkmods3.py 175, gen/kernel/mktab3.py 161, gen/kernel/mkw3.py 44 (total 484 lines)
Theorem 1.1 (v2, 643d947): closure of QEC.Checks.Thm11V3 432 project modules, of QEC.ChecksN.Thm11V2 52
  kernel-only  generated aggregator (gen/gen_agg.py)                 1 files    1061 lines
  kernel-only  generated check module (gen/gen_checks.py)          390 files    3120 lines
  kernel-only  hand-written theorem file (in a check directory)      1 files      28 lines
  native-only  generated aggregator (gen/gen_agg.py)                 1 files      89 lines
  native-only  generated check module (gen/gen_checks.py)           10 files     210 lines
  native-only  hand-written theorem file (in a check directory)      1 files      25 lines
  shared       hand-written                                         40 files    7842 lines
  generator gen/gen_checks.py: 47 lines
  generator gen/gen_agg.py: 77 lines
```

The Theorem 1.1 split comes from the import closures, restricted to project modules, of QEC.Checks.Thm11V3 and
QEC.ChecksN.Thm11V2. counts/thm11_closure_v2.tsv lists one line per module with its kind and lines.
