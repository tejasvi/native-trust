# `x * 3 = x + x + x` with the bv_decide route of Section 7 (comparison with lean-dedep's `in_kernel bv_decide` table)

Goal per file: `theorem mul_three (x : BitVec w) : x * 3 = x + x + x := by bv_decide`, then
`bvs4_kernelize mul_three` (adds `mul_three.bvs4`, same statement) and `#print axioms mul_three.bvs4`.

Setup: Lean v4.33.1 on a shared 96-core machine, the final pipeline (`BVS.Driver4`);
one `lean` process per file, `LEAN_NUM_THREADS=1`, `ulimit -v` 40 GiB (41943040 KB), files run one at a time
(`run_dc.sh`). "Wall" is `/usr/bin/time` for the whole file (library import, core `bv_decide`, our SAT call,
certificate preparation, all kernel checks); "kernel" is the sum of the kernel checks of the base declaration
(bit-blast + CNF + clause-tree agreement) and the LRAT chunk declarations, as logged by the driver.
lean-dedep itself was not run; its numbers are quoted from its README (w = 2..6: 1, 3, 7, 17, 48 s; w = 16 did not
finish in 10 min).

| w | CNF clauses | LRAT steps | hints | kernel (base + chunks) | wall (whole file) | peak RSS | axioms of `mul_three.bvs4` |
|---|---|---|---|---|---|---|---|
| 4 | 167 | 56 | 351 | 0.14 s (0.05 + 0.07) | 0.82 s | 1.61 GB | propext, Classical.choice, Quot.sound |
| 6 | 299 | 76 | 1,022 | 0.41 s (0.15 + 0.22) | 1.08 s | 1.63 GB | same |
| 8 | 431 | 150 | 2,051 | 0.73 s (0.20 + 0.48) | 1.65 s | 1.66 GB | same |
| 16 | 959 | 267 | 5,687 | 1.65 s (0.35 + 1.23) | 2.34 s | 1.79 GB | same |
| 32 | 2,015 | 600 | 14,717 | 3.64 s (0.76 + 2.78) | 4.40 s | 2.07 GB | same |
| 64 | 4,127 | 1,640 | 42,371 | 10.97 s (1.73 + 8.99) | 11.88 s | 2.34 GB | same |
| 128 | 8,351 | 5,543 | 89,806 | 28.29 s (3.39 + 24.35) | 30.00 s | 2.64 GB | same |
| 256 | 16,799 | 21,697 | 183,793 | 72.70 s (7.31 + 63.99) | 77.49 s | 3.07 GB | same |
| 512 | 33,695 | 44,205 | 1,409,291 | 454.9 s (14.8 + 432.5) | 468.4 s | 4.85 GB | same |
| 1024 | 67,487 | 105,748 | 1,671,167 | 616.8 s (29.4 + 575.5) | 651.1 s | 7.75 GB | same |

Notes.
- Every row re-proved `mul_three` with the identical statement; `#print axioms mul_three.bvs4` printed
  `[propext, Classical.choice, Quot.sound]` for all eight widths (logs: `logs/DC_w<w>.log`).
- Our bit-blaster does not merge the two adders (no gate-level hashing), so even small widths need a SAT
  certificate; its size grows about linearly up to w = 256, then jumps (1.41M hints at 512, 1.67M at 1024).
  Kernel time follows the hints: 0.2-0.35 ms per hint, plus a base check of about 0.45 ms per clause.
- Widths 4-64 were requested; 128 was requested if 64 finished under 10 min (it took 11.9 s); 256-1024 are extra.
- Same goal and settings as lean-dedep's table (single-threaded, 40 GB address space), different machine.
