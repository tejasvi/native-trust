Module runs (one process per module copy, Elab.async off; D = original with bv_decide, K = bv_kdecide):

| package | copy | D: wall, peak | K: wall, peak |
|---|---|---|---|
| veir | ArithToLLVM | 1 s, 0.83 GiB | 12 s, 1.02 GiB |
| veir | ISelA | 47 s, 1.76 GiB | 2554 s, 9.06 GiB |
| veir | ISel_sdivwPow2_neg_refinement | - | 1674 s, 15.29 GiB |
| veir | ISel_sdivwPow2_pos_refinement | - | 1043 s, 14.30 GiB |
| veir | ISel_sshlSat_refinement | - | 916 s, 13.49 GiB |
| veir | Memory | 1 s, 0.82 GiB | 1 s, 0.84 GiB |
| veir | PBVExamples | 1 s, 0.79 GiB | 82 s, 2.02 GiB |
| veir | RISCVCombinesProofs | 2 s, 0.79 GiB | 23 s, 0.91 GiB |
| veir | Combine | 10 s, 1.12 GiB | 462 s, 2.85 GiB |
| veir | ISel_sdivPow2Exact_neg_refinement | - | 3108 s, 16.77 GiB |
| veir | ISel_sdivPow2Exact_pos_refinement | - | 1756 s, 15.01 GiB |
| veir | ISel_sdivwPow2Exact_neg_refinement | - | 2034 s, 12.07 GiB |
| veir | ISel_sdivwPow2Exact_pos_refinement | - | 2030 s, 11.93 GiB |
| clean | And8 | 3 s, 1.54 GiB | 4 s, 1.79 GiB |
| clean | Bitwise | 9 s, 1.19 GiB | 1 s, 1.46 GiB |
| clean | Or8 | 3 s, 1.55 GiB | 4 s, 1.76 GiB |
| clean | ByteDecomposition | 4 s, 1.67 GiB | 285 s, 6.69 GiB |
| natuvea_model | CompositeHeader | 1 s, 0.67 GiB | 50 s, 7.07 GiB |
| natuvea_proofs | Serialization | 1 s, 0.67 GiB | 2 s, 1.52 GiB |
| asi | StackBoundaries | 1 s, 0.68 GiB | 3 s, 1.63 GiB |

Earlier runs of these copies that failed (bugs fixed since; the rows above are the reruns):
- veir Combine: rc 1 after 436 s
- veir ISel_sdivwPow2Exact_neg_refinement: rc 1 after 239 s
- veir ISel_sdivwPow2Exact_pos_refinement: rc 1 after 222 s
- clean ByteDecomposition: rc 1 after 270 s

Facts (bv_kdecide calls with a SAT call = native axioms of the originals): 195
- asi: 1 facts; bv_decide phase median 163 ms (max 163); bv_kdecide median 1.26 s, p90 1.3 s, max 1.3 s, total 1 s; peak RSS per call median 1.63 GiB, max 1.63 GiB
- clean: 4 facts; bv_decide phase median 78 ms (max 1945); bv_kdecide median 1.84 s, p90 2.0 s, max 267.7 s, total 272 s; peak RSS per call median 1.75 GiB, max 6.69 GiB
- natuvea_model: 2 facts; bv_decide phase median 154 ms (max 209); bv_kdecide median 23.97 s, p90 1.9 s, max 46.1 s, total 48 s; peak RSS per call median 7.86 GiB, max 8.68 GiB
- natuvea_proofs: 1 facts; bv_decide phase median 70 ms (max 70); bv_kdecide median 0.19 s, p90 0.2 s, max 0.2 s, total 0 s; peak RSS per call median 1.50 GiB, max 1.50 GiB
- veir: 187 facts; bv_decide phase median 58 ms (max 7071); bv_kdecide median 2.03 s, p90 53.1 s, max 2888.8 s, total 14456 s; peak RSS per call median 1.85 GiB, max 16.77 GiB

Budget curve (a fact is rewritten if its bv_kdecide time is at most the budget; added time = bv_kdecide - bv_decide):

| budget per fact | facts rewritten | of | added build time |
|---|---|---|---|
| 1 s | 64 | 195 | 14 s |
| 5 s | 135 | 195 | 172 s |
| 10 s | 148 | 195 | 263 s |
| 30 s | 166 | 195 | 626 s |
| 60 s | 176 | 195 | 1018 s |
| 120 s | 184 | 195 | 1860 s |
| 300 s | 186 | 195 | 2287 s |
| 600 s | 188 | 195 | 3242 s |
| 1800 s | 192 | 195 | 8118 s |
| none | 195 | 195 | 14724 s |

The 25 most expensive facts:

| package | module | declaration | bv_decide | bv_kdecide | peak | clauses | hints | split | cert bytes |
|---|---|---|---|---|---|---|---|---|---|
| veir | InstructionSelection.Proofs | sdivPow2Exact_neg_refinement | 4.67 s | 2888.8 s | 16.77 GiB | 854,213 | 8,702,292 | 10 | 37497181 |
| veir | InstructionSelection.Proofs | sdivwPow2Exact_neg_refinement | 4.49 s | 1871.5 s | 12.07 GiB | 592,376 | 4,729,590 | 7 | 30083081 |
| veir | InstructionSelection.Proofs | sdivwPow2Exact_pos_refinement | 5.30 s | 1860.7 s | 11.93 GiB | 588,299 | 4,571,438 | 7 | 32655582 |
| veir | InstructionSelection.Proofs | sdivPow2Exact_pos_refinement | 5.27 s | 1603.2 s | 15.00 GiB | 848,183 | 2,274,375 | 10 | 21688459 |
| veir | InstructionSelection.Proofs | sdivwPow2_neg_refinement | 7.07 s | 1528.9 s | 15.29 GiB | 174,050 | 5,433,741 | - | 45695901 |
| veir | InstructionSelection.Proofs | sdivwPow2_pos_refinement | 6.16 s | 944.0 s | 14.29 GiB | 172,205 | 3,049,348 | - | 59299824 |
| veir | InstructionSelection.Proofs | sshlSat_refinement | 0.69 s | 818.4 s | 13.49 GiB | 155,348 | 2,583,811 | - | 5345927 |
| veir | InstructionSelection.Proofs | ushlSat_refinement | 0.69 s | 484.9 s | 9.73 GiB | 91,808 | 1,483,947 | - | 6656842 |
| veir | InstructionSelection.Proofs | ashr_refinement | 0.06 s | 471.1 s | 4.17 GiB | 41,438 | 958,895 | - | 144387 |
| clean | ByteDecomposition | soundness | 1.95 s | 267.7 s | 6.69 GiB | 65,720 | 959,442 | - | 20603159 |
| veir | Combine | sextw_cpop | 0.04 s | 161.6 s | 8.81 GiB | 97,733 | 276,776 | - | 10 |
| veir | InstructionSelection.Proofs | fshl_rori_refinement | 0.33 s | 119.4 s | 6.55 GiB | 31,724 | 319,978 | - | 1777896 |
| veir | InstructionSelection.Proofs | fshl_rol_refinement | 0.34 s | 117.8 s | 6.14 GiB | 31,724 | 324,193 | - | 1775417 |
| veir | InstructionSelection.Proofs | fshr_rori_refinement | 0.33 s | 117.0 s | 6.47 GiB | 31,724 | 300,026 | - | 1877331 |
| veir | InstructionSelection.Proofs | fshr_ror_refinement | 0.33 s | 116.4 s | 6.33 GiB | 31,724 | 300,026 | - | 1877331 |
| veir | InstructionSelection.Proofs | fshlGeneral_refinement | 0.36 s | 114.3 s | 6.74 GiB | 31,610 | 268,913 | - | 2069439 |
| veir | InstructionSelection.Proofs | fshrGeneral_refinement | 0.34 s | 107.8 s | 6.93 GiB | 31,610 | 271,401 | - | 1843529 |
| veir | PBVExamples | trace_append | 0.06 s | 76.7 s | 2.02 GiB | 13,820 | 371,430 | - | 127515 |
| veir | InstructionSelection.Proofs | usubSat_refinement | 0.21 s | 75.1 s | 3.08 GiB | 12,059 | 207,946 | - | 1099585 |
| veir | InstructionSelection.Proofs | sdivPow2_neg_refinement | 0.32 s | 55.2 s | 2.62 GiB | 13,874 | 187,304 | - | 3937268 |
| veir | InstructionSelection.Proofs | sdivPow2_pos_refinement | 0.29 s | 53.1 s | 2.56 GiB | 13,892 | 188,905 | - | 3829997 |
| natuvea_model | CompositeHeader | readBe64_be64 | 0.21 s | 46.1 s | 8.68 GiB | 56,111 | 7,142 | - | 217713 |
| veir | InstructionSelection.Proofs | ashr_refinement_32 | 0.18 s | 43.3 s | 4.66 GiB | 11,204 | 147,488 | - | 33334 |
| veir | Combine | drop_sextw_rorw | 0.07 s | 33.7 s | 2.94 GiB | 16,835 | 102,081 | - | 9185 |
| veir | Combine | drop_zextw_rorw | 0.10 s | 33.6 s | 2.84 GiB | 16,835 | 102,081 | - | 9185 |
