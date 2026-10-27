# Axioms of the conversions by staging

`prove_native_axiom_nth` checks the axioms of every theorem it adds, except on the staged route without
splitting: there the theorem for the original term is a bridge from the staged check, and it is added
without that check (`NativeTrust/Kernel.lean`, `proveTrueStaged`). This route converted eight facts in the option
runs: the seven converted in run `c22s` (`stage` alone) and TrainVerify's fact converted in run `lr6` (staging applied
with the other options on, in one piece). After the runs, each was proved again with the file used in its run,
together with a check of the axioms of the theorem named on its PROVED line. The check is `#print axioms`.
TrainVerify's theorem name is private and has a numeric component, so for it the check searches for the theorem by the
end of its name and runs `Lean.collectAxioms`; it prints the result in the same form. The build, toolchains and import
paths are the same as in the runs, and each fact ran in its own process with a 16 GiB memory limit.

| file | fact | toolchain | axioms |
|---|---|---|---|
| `s_Rob1Ham_btc_lean_spec_proofs__F2_BitcoinProofs_Property_Y10_MerkleProps_23` | btc `casea23` | v4.35.0 | `propext`, `Classical.choice`, `Quot.sound` |
| `s_Rob1Ham_btc_lean_spec_proofs__F2_BitcoinProofs_Property_Y10_MerkleProps_38` | btc `casea24` | v4.35.0 | `propext`, `Classical.choice`, `Quot.sound` |
| `s_zcash_ironwood__F2_Zcash_Snark_Fixtures_PostNu63_10` | zcash `captures_use_same_ursG` | v4.30.0 | `propext`, `Classical.choice`, `Quot.sound` |
| `s_zcash_ironwood__F2_Zcash_Snark_Fixtures_PostNu63Random_5` | zcash `randomMulti_uses_same_ursG` | v4.30.0 | `propext`, `Classical.choice`, `Quot.sound` |
| `s_zcash_ironwood__F2_Zcash_Snark_Fixtures_PostNu63Random_12` | zcash `randomSingle_uses_same_ursG` | v4.30.0 | `propext`, `Classical.choice`, `Quot.sound` |
| `sounio__F2_FanoLabellingOrbits_0` | sounio `lagrange_consistency` | v4.30.0-rc2 | `propext` |
| `sounio__F2_FanoLabellingOrbits_2` | sounio `fano_labelling_orbits_count` | v4.30.0-rc2 | `propext` |
| `trainverify__F2_denote_yoco_goals_Goal4LateScopedBridge_3` | TrainVerify `goal4Late_pm_filter_eq` | v4.32.2 | `propext`, `Quot.sound` |

Each `.lean` file is the file used in its run, with the check appended; each `.log` holds the command, the PROVED
line, the axiom line and the exit status.
