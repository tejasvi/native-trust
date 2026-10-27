# mm3: rank 333 over F2, native version (not run)

The native facts are 4,381,024 batch axioms, one per batch (`rank333-f2` README.md:16-20). The run summary
`data/run/run_summary.json` records `batches` 4381024, `wall_hours` 20.95, `vcpu_hours` 478076 and `cpu_hours` 0. CPU
time was not recorded, and the vCPU-hours are the provisioned capacity of the fleet.

It was not run because the batch modules do not exist outside the run: "The certificates are regenerated and checked
in a stream, and they are not stored" (README.md:16-17). Custom commands (`lean/R1/NDB.lean`, `lean/R22N/Drv.lean`,
both through `Lean.Meta.nativeEqTrue`) write each batch module from items that the C++ generators and the queue
produce (`cpp/`, `scripts/native/nchk_batch.sh`). A sample would need that pipeline and the toolchain v4.30.0 with its
Mathlib, and the study machine (no network) has neither.

The hand-built kernel track is `rank333-f2-kernel`. Its README (line 160) says: "the module builds of the final set
took about 530,000 vCPU-hours (529,504 CPU-hours of elaboration and kernel checking, summed over all modules)". This is
the kernel build and check of the final proof, without the search and without the generation of the certificates.

Without a run, the averages compare as follows. The kernel track spent 529,504 CPU-h / 4,381,024 = 0.12 CPU-h
(435 CPU-s) of kernel-oriented checking per native batch. The native run spent 478,076 vCPU-h / 4,381,024 = 393 vCPU-s
per batch, including the regeneration of the certificates.
