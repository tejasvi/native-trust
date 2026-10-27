# Chvatal-Sankoff v5, h = 13 (not run)

The paper's bound `gamma2 <= 0.821963` (`CS31aData.gamma2_le_n13`) rests on 56 `native_decide` axioms, one per share
(README.md:303). The bound `gamma2 <= 0.822579` (h = 12) has both a native proof (7 axioms) and the kernel-only proof
`CS31aK.H12.gamma2_le` (README.md:304-308).

Hand-built kernel tracks exist only for h <= 12, a weaker bound. Their costs are kernel builds of the shard modules:
about 1,900 CPU-h for h = 9 (README.md:438), about 21,100 for h = 10 (README.md:464), about 8,800 for h = 11
(README.md:502-503) and about 69,000 for h = 12, of which 59,513 were measured (README.md:531-535).

It was not run because, in compiled code, each share "needs about 2,350 GiB of memory, since it decodes the whole
compact certificate and maps the compiled part modules (about 1.2 TB)" (README.md:398-400). The 56 shares took 23,802
CPU-hours on 22 machines with 360 virtual CPUs and 2,880 GiB each (README.md:407-408), and the pieces take
1,181,341,372,768 bytes (README.md:404). None of this fits the per-fact limits of this study or the study machine.
