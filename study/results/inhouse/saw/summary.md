# SAW connective constant v5 (not run)

The 169 `native_decide` facts in `k28f` and the 3 controls have no hand-built kernel track.

They were not run because they read the certificate `k30e`: "The build reads the three files of `k30e` ... and
converts them into 11,497 Lean data files (796.4 GB) of at most 2,164,802 states. Lean compiles these into five shared
libraries of about 800 GB in all; linking them uses about 320 GB of memory, and the build needs about 5.6 TB of disk
space besides the decompressed certificate" (README.md:277-280). The study machine has about 84 GB of free disk, and
the certificate is in the Zenodo records. In the kernel, the 796.4 GB of data would have to be terms.

The release states the native cost: "The proof then runs 180 checking steps of at most 138,547,328 states each. They
took about 1.2 × 10^6 CPU-seconds, or about 3.3 hours on one machine with 128 threads and about 2 TB of memory"
(README.md:280-281).
