# BHH TSP constant v8 (not run)

The two strongest Lean results rest on native checks only. `lean/native/` proves `beta >= 0.6491725104` with 5,536
`native_decide` axioms: 5,520 ranges of initial boxes, 6 table checks and 10 checks of the window-two bound
(README.md:288-296). `lean/native_v3/` proves `beta >= 0.6496497227` with 5,671 axioms (`axioms_N3W20.txt`,
README.md:265-276).

The hand-built kernel track, `lean/kernel/`, proves the weaker `beta >= 0.6440396` (README.md:297-303). Its cost is the
kernel build of the 105,255 generated modules: "Building the generated modules of `C_3` and `C_4` took about 5,250
hours of single-threaded time in total, and those of `C_5` about 9,570 hours" (README.md:309-310).

It was not run because "Evaluating the 5,520 ranges took about three hours on up to 60 machines with 96 threads each"
(README.md:295-296). That is up to about 17,000 thread-hours, about 3 thread-hours per range in compiled code. A check
that takes hours in compiled code is far beyond the per-fact limits of this study in the kernel (900 s and 48 GiB, and
3,600 s and 96 GiB in the heavy pass).
