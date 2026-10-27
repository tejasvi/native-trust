# Evidence index for the runs of the tactic bv_kdecide

Copied from the study machine; paths below are relative to this
directory. Peak memory = KiB (from `/usr/bin/time` or `VmHWM`) / 2^20.

| claim | file(s) |
|---|---|
| 17 example theorems use only the standard axioms (r13, v4.35.0) | `bvs_r13/logs/Examples.Tactic.log` (in-file assertions), `tests_v1/Check2.log` (fresh process; `MODULE` lines: 0 `_native` names in `Examples.Tactic`, 4 in `Examples.Small`) |
| final sources build on 7 toolchains | `bvs_r13/times.tsv`, `port13_v4.*/times.tsv` (non-module); `bvsmod6_v4.*/times.tsv` (module variant); per-module output in `*/logs/` |
| module variant: audit, sharded workflow | `bvsmod6_v4.35.0/audit.log`, `bvsmod6_v4.35.0/work_ShardPrep/ShardPrep.log`, `bvsmod6_v4.35.0/work_SplitPrep/SplitPrep.log` |
| nanoda accepts the examples, rejects the bv_decide original | `nanoda/tactic_r13/` and `nanoda/negctl_r13/` (`cmd.txt`, `nanoda.log`, `nanoda.json`) |
| nanoda accepts veir theorems proved with bv_kdecide, rejects the original | `nanoda/veir_riscv_k/`, `nanoda/veir_riscv_d_negctl/` |
| per-fact times and memory (195 facts) | `real_v3/<pkg>/RealK_<copy>.progress` (one `bv_kdecide […]` line per call), `real_v4/veir/RealK_Combine.progress`, `real_v6/veir/RealK_ISel_*.progress`, `real_v6/clean/RealK_ByteDecomposition.progress`; module times in `real_v*/<pkg>/results.tsv`; table built by `../sum_real_v3.py` into `../real_facts_final.tsv` and `.md` |
| converted modules declare no `_native` name; declarations use only standard axioms | `real_v*/<pkg>/CheckK_*.lean.log`, `Check2K_*.lean.log` (and `CheckD_*`, `Check2D_*` for the originals) |
| veir one-line migration | `chain_v11.log` (lines `macro2 rc=0`, `realm2 rc=0`, `check2m2 rc=0`); `real_v5/veir/vmac/macro2.log` (empty: the changed macro module compiled without messages), `real_v5/veir/realm2.log`, `real_v5/veir/RealM_RISCVCombinesProofs.progress` (68 calls), `real_v5/veir/check2m2.log` |
| Natuvea end to end | `real_v3/natuvea_proofs/e2e_k2.log`, `real_v3/natuvea_proofs/e2e_check22.log` |
| certificate sizes of the bv_decide axioms | `real_v3/<pkg>/CertD_*.lean.log` |
| `bvs5_estimate` output on the real modules | `est_v1/Est*.lean.log` (`BVS_ESTIMATE` lines) |
| single-fact benchmark | `bench_v1/results_small.tsv`, `bench_v1/results_big3.tsv`, `bench_v1/*.lean.log`; `bench_v2/results.tsv`, `bench_v2/*.log` |
| order of the runs, memory gates | `chain_v*.log` |

Not evidence:
- `nanoda/tactic_all/` and `nanoda/negctl_small/`: first attempt; the script did not put `lean` on PATH, so
  `leanexport` produced an empty export and nanoda's "Checked 0 declarations" is vacuous. The runs used are
  `tactic_all_v2`/`negctl_small_v2` (sources r8), `tactic_r12`/`negctl_r12`, `tactic_r13`/`negctl_r13` (final).
- `bench_v1/kz_andor_w4096.lean.log`: `bv_decide` followed by `bvs4_kernelize` (not the tactic) stops with
  "(kernel) deep recursion detected" unless the file sets `maxRecDepth`; the tactic raises it itself.
- Runs of copies that failed before a fix (listed in `../real_facts_final.md`) and builds `bvs_v1`,
  `bvs_v1_r2`, `bvs_r8`, `port12_*`, `bvsmod2/3/5_*`: earlier revisions, kept for the history.
