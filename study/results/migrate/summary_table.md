| package | toolchain | uses | replaced (with facts + examples) | remaining | facts converted | native axioms before → after | native-dependent decls before → after | rewritten decls still native | build ok | affected modules | wall s before → after | CPU s before → after |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| lido-srv3 | v4.31.0 | 372 | 332 (70 + 262) | 40 | 70 of 70 | 70 → 0 | 84 → 0 | 0 of 68 | yes | 26 | 7.8 → 15.6 | 32.2 → 42.6 |
| cvc5-logos | v4.34.0 | 606 | 605 (605 + 0) | 1 | 2184 of 2185 | 2185 → 1 | 3157 → 1483 | 49 of 412 | yes | 204 | 1854.5 → 1717.3 | 5723.4 → 5270.9 |
| humanfia-icho2026 | v4.31.0 | 693 | 673 (673 + 0) | 20 | 1719 of 1864 | 1864 → 145 | 424 → 25 | 9 of 270 | yes | 34 | 94.5 → 469.5 | 506.0 → 1214.3 |
| humanfia-icho2026-bump | v4.31.0 | 693 | 689 (689 + 0) | 4 | 1860 of 1864 | 1864 → 4 | 424 → 12 | 6 of 272 | yes | 34 | 116.1 → 501.0 | 483.9 → 1161.0 |
| asi-stack-book | v4.31.0 | 382 | 374 (374 + 0) | 8 | 382 of 392 | 392 → 10 | 366 → 10 | 1 of 351 | yes | 55 | 29.7 → 28.7 | 138.9 → 138.0 |
| sounio | v4.30.0-rc2 | 741 | 70 (70 + 0) | 671 | 70 of 77 | 77 → 7 | 90 → 10 | 0 of 68 | yes | 15 | 6.8 → 205.0 | 16.0 → 226.1 |
| formal-conjectures | v4.33.1 | 209 | 166 (155 + 11) | 43 | 579 of 690 | 690 → 111 | 172 → 40 | 0 of 135 | yes | 43 | 44.8 → 210.7 | 176.0 → 639.1 |
| s_justrach_codegraff_lean_proofs | v4.33.0 | 235 | 178 (65 + 113) | 57 | 74 of 88 | 88 → 14 | 80 → 14 | 0 of 65 | yes | 10 | 1.6 → 181.8 | 6.7 → 196.7 |
| s_batmeezy918_chronofold | v4.29.0 | 11 | 11 (11 + 0) | 0 | 11 of 11 | 11 → 0 | 11 → 0 | 0 of 9 | yes | 1 | 0.6 → 0.6 | 0.7 → 0.8 |
| s_dappalumbo91_FSOT_2_1_Neural_formal | v4.31.0 | 52 | 52 (52 + 0) | 0 | 118 of 118 | 118 → 0 | 46 → 0 | 0 of 46 | yes | 11 | 1.2 → 1.9 | 2.9 → 3.9 |
| s_Rob1Ham_btc_lean_spec_proofs | v4.35.0 | 833 | 132 (3 + 129) | 701 | 3 of 134 | 134 → 131 | 134 → 131 | 0 of 3 | yes | 12 | 55.5 → 265.1 | 79.5 → 516.0 |
| **total** (without -bump rows) | | 4134 | 2593 | 1541 | 5210 of 5629 | 5629 → 419 | 4564 → 1713 | | | | | |

**lido-srv3** remaining: 28 module build over the round limit (300 s); 12 module not built in the original
**cvc5-logos** remaining: 1 kernel blocked at WellFounded.fix (per-fact result)
  rewritten declarations still native: 49: depends on another native-dependent declaration
**humanfia-icho2026** remaining: 16 over maxHeartbeats after the rewrite (opt-in --bump-heartbeats); 3 kernel out of memory (per-fact result); 1 kernel over the per-fact time limit 900s (per-fact result)
  rewritten declarations still native: 5: depends on another native-dependent declaration; 1: 1 unconverted native facts of its own; 1: 2 unconverted native facts of its own; 2: 4 unconverted native facts of its own
**humanfia-icho2026-bump** remaining: 3 kernel out of memory (per-fact result); 1 kernel over the per-fact time limit 900s (per-fact result)
  rewritten declarations still native: 3: depends on another native-dependent declaration; 2: 1 unconverted native facts of its own; 1: 2 unconverted native facts of its own
**asi-stack-book** remaining: 8 kernel stuck (cast in a Decidable instance) (per-fact result)
  rewritten declarations still native: 1: 1 unconverted native facts of its own
**sounio** remaining: 664 module not built in the original; 4 kernel over the per-fact time limit 900s (per-fact result); 2 kernel out of memory (per-fact result); 1 kernel blocked at Float.decLe (per-fact result)
**formal-conjectures** remaining: 18 kernel blocked at WellFounded.fix (per-fact result); 9 kernel over the per-fact time limit 900s (per-fact result); 7 kernel out of memory (per-fact result); 2 module not built in the original; 2 kernel deep recursion in the build; 2 kernel stuck (cast in a Decidable instance) (per-fact result); 1 over maxHeartbeats after the rewrite (opt-in --bump-heartbeats); 1 decide +kernel failed in the build; 1 kernel max recursion depth (per-fact result)
**s_justrach_codegraff_lean_proofs** remaining: 32 decide +kernel failed in the build; 19 module not built in the original; 5 kernel blocked at WellFounded.extrinsicFix₃ (per-fact result); 1 kernel deep recursion in the build
**s_batmeezy918_chronofold** remaining: 
**s_dappalumbo91_FSOT_2_1_Neural_formal** remaining: 
**s_Rob1Ham_btc_lean_spec_proofs** remaining: 599 module build over the round limit (600 s); 99 module not built in the original; 3 kernel out of memory (per-fact result)
