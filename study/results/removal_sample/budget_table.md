# Per-fact budget for `ntrust migrate`: trade-off on the 24 random-sample packages

Unbudgeted = the final table (rows s2/c2/s). Budget HB = `--fact-budget HB` (thousands of heartbeats): a use is rewritten only if every fact behind it is REPLACEABLE in `#native_decide_audit` under HB; examples are tried in the build rounds within the same budget. Times: clean rebuilds of the affected modules (time0 → time1), packages where some module was rebuilt. "> 2×" = packages whose affected modules take more than twice as long (and 5 s more).

| run | packages | uses replaced pooled | median | native axioms removed pooled | median | wall ratio pooled | median | CPU ratio pooled | median | worst wall ratio | packages > 2× slower | builds OK (+pinning only, failures) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| no budget (earlier table) | 24 | 50.0% (1180/2361) | 80.7% | 53.6% (789/1472) | 75.9% | 5.38 | 1.87 | 5.47 | 1.69 | 143.50 (justrach_codegraff_lean_proofs, 1.34 → 192.29 s) | 9 of 20 | 23 (+1, 0) |
| **v14, defaults: budget 2000 + max-slowdown 2** | 24 | 28.1% (664/2361) | 47.2% | 30.1% (443/1472) | 25.0% | 0.99 | 1.00 | 0.99 | 1.00 | 1.69 (dappalumbo91_FSOT_2_1_Neural_formal, 1.03 → 1.74 s) | 0 of 19 | 23 (+1, 0) |
| v13, defaults (comparison) | 24 | 27.7% (655/2361) | 47.2% | 30.3% (446/1472) | 25.0% | 0.98 | 0.99 | 1.00 | 1.00 | 1.48 (dappalumbo91_FSOT_2_1_Neural_formal, 1.84 → 2.73 s) | 0 of 19 | 23 (+1, 0) |
| budget 2000 only | 24 | 48.5% (1145/2361) | 63.4% | 38.2% (562/1472) | 28.2% | 1.30 | 1.01 | 1.33 | 1.03 | 5.31 (Rob1Ham_btc_lean_spec_runners, 8.17 → 43.38 s) | 2 of 19 | 23 (+1, 0) |
| budget 20000 only | 24 | 47.6% (1124/2361) | 74.2% | 51.2% (754/1472) | 45.5% | 2.27 | 1.03 | 2.32 | 1.05 | 9.52 (Natuvea_tacenta_core_tacenta_model, 12.86 → 122.46 s) | 6 of 19 | 23 (+1, 0) |
| budget 200 only | 24 | 34.3% (811/2361) | 49.7% | 29.3% (431/1472) | 18.6% | 1.00 | 1.00 | 1.00 | 1.00 | 1.50 (RianKoja_novacula, 0.22 → 0.33 s) | 0 of 19 | 23 (+1, 0) |

max-slowdown reverts in the v14 defaults run: Provenance_Works_Radix 1 module(s), Rob1Ham_btc_lean_spec_proofs 7 module(s), justrach_codegraff_lean_proofs 1 module(s), Rob1Ham_btc_lean_spec_runners 1 module(s), V_Sekai_fire_interactor_spatial_oracle 2 module(s), Natuvea_tacenta_core_tacenta_model 3 module(s)

## v14, defaults (budget 2000 + max-slowdown 2); in brackets: no budget

| package | uses replaced (facts) | native axioms before → after (unbudgeted after) | build ok | wall s before → after (unbudgeted after) | audit verdicts |
|---|---|---|---|---|---|
| zcash_ironwood | 104 of 328 (104) | 332 → 228 (77) | axiom-pinning check only | 89.5 → 86.8 (836.5) | EXPENSIVE 210, REPLACEABLE 113, BLOCKED 4, STUCK 1 |
| emberian_minidregg | 5 of 246 (5) | 228 → 223 (219) | yes | 9.7 → 10.1 (443.7) | EXPENSIVE 95, BLOCKED 71, REPLACEABLE 59, STUCK 2, NATIVETRUST 1 |
| opencompl_veir | 2 of 2 (0) | 188 → 188 (188) | yes | 6.8 → 6.7 (7.1) | BLOCKED 188 |
| Provenance_Works_Radix | 163 of 218 (76) | 145 → 69 (18) | yes | 116.6 → 117.6 (285.5) | REPLACEABLE 124, BLOCKED 17, EXPENSIVE 4 |
| Rob1Ham_btc_lean_spec_proofs | 28 of 833 (3) | 134 → 131 (85) | yes | 53.2 → 54.9 (816.5) | EXPENSIVE 118, REPLACEABLE 16 |
| dappalumbo91_FSOT_2_1_Neural_formal | 52 of 52 (118) | 118 → 0 (0) | yes | 1.0 → 1.7 (2.2) | REPLACEABLE 118 |
| justrach_codegraff_lean_proofs | 146 of 235 (58) | 88 → 30 (14) | yes | 1.3 → 1.6 (192.3) | REPLACEABLE 65, EXPENSIVE 11, NATIVETRUST 7, BLOCKED 5 |
| Rob1Ham_btc_lean_spec_runners | 0 of 111 (0) | 63 → 63 (0) | yes | 7.8 → 8.0 (51.9) | REPLACEABLE 61, EXPENSIVE 2 |
| V_Sekai_fire_interactor_spatial_oracle | 29 of 43 (29) | 43 → 14 (7) | yes | 2.0 → 1.9 (10.2) | REPLACEABLE 34, EXPENSIVE 8, NATIVETRUST 1 |
| cedar_policy_cedar_spec_cedar_lean | 10 of 26 (10) | 26 → 16 (16) | yes | 1.0 → 1.0 (1.1) | BLOCKED 16, REPLACEABLE 10 |
| FrederickPu_Zag | 4 of 45 (3) | 23 → 20 (19) | yes | 3.0 → 3.0 (10.2) | BLOCKED 19, REPLACEABLE 3, NATIVETRUST 1 |
| BobDyLean_bobdylean_paper_artifact | 0 of 14 (0) | 14 → 14 (14) | yes | n/a (no module rebuilt) (n/a) | STUCK 10 |
| sun123zxy_ninegates_lean4 | 0 of 9 (0) | 14 → 14 (14) | yes | n/a (no module rebuilt) (n/a) | NATIVETRUST 6, EXPENSIVE 1 |
| moggedhedien_rimalloc_verify | 3 of 12 (3) | 12 → 9 (5) | yes | 35.0 → 34.2 (269.5) | EXPENSIVE 9, REPLACEABLE 3 |
| batmeezy918_chronofold | 11 of 11 (11) | 11 → 0 (0) | yes | 0.6 → 0.6 (0.9) | REPLACEABLE 11 |
| clementefalcone_goya_ledger_formal | 9 of 10 (9) | 10 → 1 (1) | yes | 0.6 → 0.6 (0.7) | REPLACEABLE 9, EXPENSIVE 1 |
| rusch95_cakec_proofs_lean | 8 of 8 (9) | 9 → 0 (0) | yes | 3.6 → 3.4 (3.8) | REPLACEABLE 9 |
| leanprover_community_physlib | 1 of 4 (1) | 4 → 3 (1) | yes | n/a (no module rebuilt) (n/a) | EXPENSIVE 3, REPLACEABLE 1 |
| WyattAu_OmniLaTeX_template_specs_proofs | 3 of 3 (3) | 3 → 0 (0) | yes | 0.2 → 0.2 (0.2) | REPLACEABLE 3 |
| Natuvea_tacenta_core_tacenta_model | 79 of 141 (0) | 2 → 2 (2) | yes | 12.6 → 10.4 (729.3) | BLOCKED 2 |
| pandaman64_lean_regex_correctness | 0 of 2 (0) | 2 → 2 (2) | yes | n/a (no module rebuilt) (n/a) | BLOCKED 2 |
| Flaman55_StructuralSieve | 0 of 1 (0) | 1 → 1 (0) | yes | n/a (no module rebuilt) (39.9) | EXPENSIVE 1 |
| Natuvea_tacenta_core_tacenta_proofs | 6 of 6 (0) | 1 → 1 (1) | yes | 2.2 → 1.2 (1.5) | BLOCKED 1 |
| RianKoja_novacula | 1 of 1 (1) | 1 → 0 (0) | yes | 0.2 → 0.3 (0.3) | REPLACEABLE 1 |

## v13, budget 2000 only

| package | uses replaced (facts) | native axioms before → after (unbudgeted after) | build ok | wall s before → after (unbudgeted after) | audit verdicts |
|---|---|---|---|---|---|
| zcash_ironwood | 104 of 328 (104) | 332 → 228 (77) | axiom-pinning check only | 88.1 → 87.5 (836.5) | EXPENSIVE 210, REPLACEABLE 113, BLOCKED 4, STUCK 1 |
| emberian_minidregg | 5 of 246 (5) | 228 → 223 (219) | yes | 9.4 → 9.9 (443.7) | EXPENSIVE 95, BLOCKED 71, REPLACEABLE 59, NATIVETRUST 1 |
| opencompl_veir | 2 of 2 (0) | 188 → 188 (188) | yes | 7.0 → 7.0 (7.1) | BLOCKED 188 |
| Provenance_Works_Radix | 199 of 218 (109) | 145 → 36 (18) | yes | 119.4 → 120.2 (285.5) | REPLACEABLE 109, BLOCKED 32, EXPENSIVE 4 |
| Rob1Ham_btc_lean_spec_proofs | 360 of 833 (16) | 134 → 118 (85) | yes | 54.3 → 114.2 (816.5) | EXPENSIVE 118, REPLACEABLE 16 |
| dappalumbo91_FSOT_2_1_Neural_formal | 52 of 52 (118) | 118 → 0 (0) | yes | 2.0 → 2.4 (2.2) | REPLACEABLE 118 |
| justrach_codegraff_lean_proofs | 169 of 235 (65) | 88 → 23 (14) | yes | 1.4 → 3.7 (192.3) | REPLACEABLE 65, EXPENSIVE 11, NATIVETRUST 7, BLOCKED 5 |
| Rob1Ham_btc_lean_spec_runners | 61 of 111 (61) | 63 → 2 (0) | yes | 8.2 → 43.4 (51.9) | REPLACEABLE 61, EXPENSIVE 2 |
| V_Sekai_fire_interactor_spatial_oracle | 34 of 43 (34) | 43 → 9 (7) | yes | 2.8 → 4.2 (10.2) | REPLACEABLE 34, EXPENSIVE 8, NATIVETRUST 1 |
| cedar_policy_cedar_spec_cedar_lean | 10 of 26 (10) | 26 → 16 (16) | yes | 1.0 → 1.0 (1.1) | BLOCKED 16, REPLACEABLE 10 |
| FrederickPu_Zag | 4 of 45 (3) | 23 → 20 (19) | yes | 3.3 → 3.2 (10.2) | BLOCKED 19, REPLACEABLE 3, NATIVETRUST 1 |
| BobDyLean_bobdylean_paper_artifact | 0 of 14 (0) | 14 → 14 (14) | yes | n/a (no module rebuilt) (n/a) | STUCK 10 |
| sun123zxy_ninegates_lean4 | 0 of 9 (0) | 14 → 14 (14) | yes | n/a (no module rebuilt) (n/a) | BLOCKED 14 |
| moggedhedien_rimalloc_verify | 3 of 12 (3) | 12 → 9 (5) | yes | 36.0 → 36.4 (269.5) | EXPENSIVE 9, REPLACEABLE 3 |
| batmeezy918_chronofold | 11 of 11 (11) | 11 → 0 (0) | yes | 0.6 → 0.6 (0.9) | REPLACEABLE 11 |
| clementefalcone_goya_ledger_formal | 9 of 10 (9) | 10 → 1 (1) | yes | 0.6 → 0.6 (0.7) | REPLACEABLE 9, EXPENSIVE 1 |
| rusch95_cakec_proofs_lean | 8 of 8 (9) | 9 → 0 (0) | yes | 3.5 → 3.5 (3.8) | REPLACEABLE 9 |
| leanprover_community_physlib | 1 of 4 (1) | 4 → 3 (1) | yes | n/a (no module rebuilt) (n/a) | EXPENSIVE 3, REPLACEABLE 1 |
| WyattAu_OmniLaTeX_template_specs_proofs | 3 of 3 (3) | 3 → 0 (0) | yes | 0.2 → 0.2 (0.2) | REPLACEABLE 3 |
| Natuvea_tacenta_core_tacenta_model | 103 of 141 (0) | 2 → 2 (2) | yes | 14.0 → 20.7 (729.3) | BLOCKED 2 |
| pandaman64_lean_regex_correctness | 0 of 2 (0) | 2 → 2 (2) | yes | n/a (no module rebuilt) (n/a) | BLOCKED 2 |
| Flaman55_StructuralSieve | 0 of 1 (0) | 1 → 1 (0) | yes | n/a (no module rebuilt) (39.9) | EXPENSIVE 1 |
| Natuvea_tacenta_core_tacenta_proofs | 6 of 6 (0) | 1 → 1 (1) | yes | 2.1 → 1.3 (1.5) | BLOCKED 1 |
| RianKoja_novacula | 1 of 1 (1) | 1 → 0 (0) | yes | 0.2 → 0.3 (0.3) | REPLACEABLE 1 |

## v13, budget 20000 only

| package | uses replaced (facts) | native axioms before → after (unbudgeted after) | build ok | wall s before → after (unbudgeted after) | audit verdicts |
|---|---|---|---|---|---|
| zcash_ironwood | 247 of 328 (247) | 332 → 85 (77) | axiom-pinning check only | 170.8 → 415.6 (836.5) | REPLACEABLE 256, EXPENSIVE 67, BLOCKED 4, STUCK 1 |
| emberian_minidregg | 5 of 246 (5) | 228 → 223 (219) | yes | 9.7 → 10.8 (443.7) | EXPENSIVE 85, BLOCKED 71, REPLACEABLE 69, NATIVETRUST 1 |
| opencompl_veir | 2 of 2 (0) | 188 → 188 (188) | yes | 7.1 → 7.1 (7.1) | BLOCKED 188 |
| Provenance_Works_Radix | 201 of 218 (111) | 145 → 34 (18) | yes | 121.5 → 132.4 (285.5) | REPLACEABLE 111, BLOCKED 32, EXPENSIVE 2 |
| Rob1Ham_btc_lean_spec_proofs | 175 of 833 (55) | 134 → 79 (85) | yes | 55.3 → 193.7 (816.5) | EXPENSIVE 79, REPLACEABLE 55 |
| dappalumbo91_FSOT_2_1_Neural_formal | 52 of 52 (118) | 118 → 0 (0) | yes | 1.6 → 2.4 (2.2) | REPLACEABLE 118 |
| justrach_codegraff_lean_proofs | 172 of 235 (68) | 88 → 20 (14) | yes | 1.3 → 7.3 (192.3) | REPLACEABLE 68, NATIVETRUST 8, EXPENSIVE 7, BLOCKED 5 |
| Rob1Ham_btc_lean_spec_runners | 63 of 111 (63) | 63 → 0 (0) | yes | 8.3 → 48.2 (51.9) | REPLACEABLE 63 |
| V_Sekai_fire_interactor_spatial_oracle | 36 of 43 (36) | 43 → 7 (7) | yes | 2.9 → 9.2 (10.2) | REPLACEABLE 36, NATIVETRUST 7 |
| cedar_policy_cedar_spec_cedar_lean | 10 of 26 (10) | 26 → 16 (16) | yes | 1.0 → 1.0 (1.1) | BLOCKED 16, REPLACEABLE 10 |
| FrederickPu_Zag | 4 of 45 (3) | 23 → 20 (19) | yes | 3.2 → 3.1 (10.2) | BLOCKED 19, REPLACEABLE 3, NATIVETRUST 1 |
| BobDyLean_bobdylean_paper_artifact | 0 of 14 (0) | 14 → 14 (14) | yes | n/a (no module rebuilt) (n/a) | STUCK 14 |
| sun123zxy_ninegates_lean4 | 0 of 9 (0) | 14 → 14 (14) | yes | n/a (no module rebuilt) (n/a) | BLOCKED 14 |
| moggedhedien_rimalloc_verify | 3 of 12 (3) | 12 → 9 (5) | yes | 34.9 → 35.6 (269.5) | EXPENSIVE 9, REPLACEABLE 3 |
| batmeezy918_chronofold | 11 of 11 (11) | 11 → 0 (0) | yes | 0.6 → 0.6 (0.9) | REPLACEABLE 11 |
| clementefalcone_goya_ledger_formal | 9 of 10 (9) | 10 → 1 (1) | yes | 0.6 → 0.6 (0.7) | REPLACEABLE 9, EXPENSIVE 1 |
| rusch95_cakec_proofs_lean | 8 of 8 (9) | 9 → 0 (0) | yes | 3.5 → 3.4 (3.8) | REPLACEABLE 9 |
| leanprover_community_physlib | 2 of 4 (2) | 4 → 2 (1) | yes | n/a (no module rebuilt) (n/a) | REPLACEABLE 2, EXPENSIVE 2 |
| WyattAu_OmniLaTeX_template_specs_proofs | 3 of 3 (3) | 3 → 0 (0) | yes | 0.2 → 0.2 (0.2) | REPLACEABLE 3 |
| Natuvea_tacenta_core_tacenta_model | 114 of 141 (0) | 2 → 2 (2) | yes | 12.9 → 122.5 (729.3) | BLOCKED 2 |
| pandaman64_lean_regex_correctness | 0 of 2 (0) | 2 → 2 (2) | yes | n/a (no module rebuilt) (n/a) | BLOCKED 2 |
| Flaman55_StructuralSieve | 0 of 1 (0) | 1 → 1 (0) | yes | n/a (no module rebuilt) (39.9) | EXPENSIVE 1 |
| Natuvea_tacenta_core_tacenta_proofs | 6 of 6 (0) | 1 → 1 (1) | yes | 2.1 → 1.3 (1.5) | BLOCKED 1 |
| RianKoja_novacula | 1 of 1 (1) | 1 → 0 (0) | yes | 0.3 → 0.3 (0.3) | REPLACEABLE 1 |

## v13, budget 200 only

| package | uses replaced (facts) | native axioms before → after (unbudgeted after) | build ok | wall s before → after (unbudgeted after) | audit verdicts |
|---|---|---|---|---|---|
| zcash_ironwood | 80 of 328 (80) | 332 → 252 (77) | axiom-pinning check only | 146.6 → 145.7 (836.5) | EXPENSIVE 234, REPLACEABLE 89, BLOCKED 4, STUCK 1 |
| emberian_minidregg | 3 of 246 (3) | 228 → 225 (219) | yes | 7.6 → 7.8 (443.7) | EXPENSIVE 117, BLOCKED 71, REPLACEABLE 22 |
| opencompl_veir | 2 of 2 (0) | 188 → 188 (188) | yes | 6.9 → 6.9 (7.1) | BLOCKED 188 |
| Provenance_Works_Radix | 175 of 218 (85) | 145 → 60 (18) | yes | 124.5 → 125.0 (285.5) | REPLACEABLE 85, BLOCKED 32, EXPENSIVE 28 |
| Rob1Ham_btc_lean_spec_proofs | 169 of 833 (9) | 134 → 125 (85) | yes | 56.6 → 57.4 (816.5) | EXPENSIVE 125, REPLACEABLE 9 |
| dappalumbo91_FSOT_2_1_Neural_formal | 50 of 52 (116) | 118 → 2 (0) | yes | 1.5 → 1.7 (2.2) | REPLACEABLE 116, EXPENSIVE 2 |
| justrach_codegraff_lean_proofs | 163 of 235 (59) | 88 → 29 (14) | yes | 2.3 → 3.2 (192.3) | REPLACEABLE 59, EXPENSIVE 20, BLOCKED 5, NATIVETRUST 4 |
| Rob1Ham_btc_lean_spec_runners | 0 of 111 (0) | 63 → 63 (0) | yes | 8.5 → 8.3 (51.9) | EXPENSIVE 63 |
| V_Sekai_fire_interactor_spatial_oracle | 30 of 43 (30) | 43 → 13 (7) | yes | 2.6 → 2.6 (10.2) | REPLACEABLE 30, EXPENSIVE 13 |
| cedar_policy_cedar_spec_cedar_lean | 10 of 26 (10) | 26 → 16 (16) | yes | 1.0 → 1.0 (1.1) | BLOCKED 16, REPLACEABLE 10 |
| FrederickPu_Zag | 4 of 45 (3) | 23 → 20 (19) | yes | 3.1 → 3.3 (10.2) | BLOCKED 19, REPLACEABLE 3, NATIVETRUST 1 |
| BobDyLean_bobdylean_paper_artifact | 0 of 14 (0) | 14 → 14 (14) | yes | n/a (no module rebuilt) (n/a) | STUCK 10 |
| sun123zxy_ninegates_lean4 | 0 of 9 (0) | 14 → 14 (14) | yes | n/a (no module rebuilt) (n/a) | BLOCKED 14 |
| moggedhedien_rimalloc_verify | 3 of 12 (3) | 12 → 9 (5) | yes | 34.5 → 34.8 (269.5) | EXPENSIVE 9, REPLACEABLE 3 |
| batmeezy918_chronofold | 11 of 11 (11) | 11 → 0 (0) | yes | 0.6 → 0.6 (0.9) | REPLACEABLE 11 |
| clementefalcone_goya_ledger_formal | 9 of 10 (9) | 10 → 1 (1) | yes | 0.6 → 0.6 (0.7) | REPLACEABLE 9, EXPENSIVE 1 |
| rusch95_cakec_proofs_lean | 8 of 8 (9) | 9 → 0 (0) | yes | 4.1 → 3.6 (3.8) | REPLACEABLE 9 |
| leanprover_community_physlib | 0 of 4 (0) | 4 → 4 (1) | yes | n/a (no module rebuilt) (n/a) | EXPENSIVE 4 |
| WyattAu_OmniLaTeX_template_specs_proofs | 3 of 3 (3) | 3 → 0 (0) | yes | 0.2 → 0.2 (0.2) | REPLACEABLE 3 |
| Natuvea_tacenta_core_tacenta_model | 86 of 141 (0) | 2 → 2 (2) | yes | 14.2 → 14.0 (729.3) | BLOCKED 2 |
| pandaman64_lean_regex_correctness | 0 of 2 (0) | 2 → 2 (2) | yes | n/a (no module rebuilt) (n/a) | BLOCKED 2 |
| Flaman55_StructuralSieve | 0 of 1 (0) | 1 → 1 (0) | yes | n/a (no module rebuilt) (39.9) | EXPENSIVE 1 |
| Natuvea_tacenta_core_tacenta_proofs | 4 of 6 (0) | 1 → 1 (1) | yes | 2.1 → 0.6 (1.5) | BLOCKED 1 |
| RianKoja_novacula | 1 of 1 (1) | 1 → 0 (0) | yes | 0.2 → 0.3 (0.3) | REPLACEABLE 1 |
