# The 80 resource failures that compare large computed values

`resv80.tsv` lists the 80 facts that the resource re-runs class as "large computed values, no structure":
minidregg (63), formal-conjectures (8), zcash (4), sounio (2), m31 (1), trainverify (1) and longfellow (1). With library v13
(`stage`, `csimp`), 30 of them had been run, and 5 of these convert. Three formal-conjectures facts convert by
csimp (`OeisA115366.a_2`, `.a_3` and `Wolstenholme_16483`), and two sounio facts convert by staging
(`lagrange_consistency` and `fano_labelling_orbits_count`). The other 75 were run on a build whose extensions to
staging were not adopted into the library. These runs used stage, csimp and propSplit with split 16, and a limit
of 900 s per fact (300 s for the last 45 minidregg facts). None of the 75 converts within 900 s.
`rv80z_classes.tsv` gives the staging profile of each fact, and `rv80z_causes.tsv` gives its cause group.

## Why the 75 do not convert

The sizes below were measured by the `#eval` commands of `sizes.lean`, whose output is `sizes.log`.

| cause | facts | size, kernel steps |
|---|---:|---|
| Arrays built by `Array.push` in `StateM` builders and then folded over. They are minidregg's Bend cSHAKE (8), Keccak (3), commitment frame (3), committed network (2), ZK-literal graph (13) and demand checks (5). | 34 | In the kernel an `Array` is a `List`, so each push copies it and each indexed read walks it. The cSHAKE network has 607,242 gates and 1,225 inputs. Building it takes about n²/2 = 1.8·10¹¹ list steps, and evaluating it takes about 3n²/2 = 5.5·10¹¹. The Keccak network has 199,768 gates, which take 2.0·10¹⁰ and 6·10¹⁰ steps. The frame (4,950 gates) and the ZK graph (1,928 gates) are small (10⁶–10⁷ steps), but their decomposition goes through the monadic builder, one `bind` per staged layer, and runs out of time. |
| The Nock `cue` of the 566,499-byte jam, in minidregg's `NockCost` (7) and `NockCost.Summaries` (11). | 18 | `cue` reads 4,531,992 bits by `B[i]?` from an array and writes a table by `setIfInBounds`, which takes about n²/2 ≈ 10¹³ steps. The jam, a list of 566,499 elements, is also over `stageSize`. |
| Codecs and hashes over byte and word arrays. They are `DurableCheckpointCodec` (4), `StoreCodec`, the `FnWire` digest, the Blake3 vectors, the `CredentialAuthority` roots (2), the `DurableIndex` probe and the `ObjectiveBend` replay. | 11 | These are long sequential runs over `ByteArray` or `Array` states, which run out of time or memory. |
| The zcash multi-scalar multiplication `evalNat` in `capturedMsm_eval(Nat)_{eq,ne}_zero`. | 4 | The sum (`Finset.sum`, now decomposed) runs over 2^11 = 2048 terms `c.val • gᵢ`. One scalar multiplication of a 250–254-bit scalar takes 10.9–12.1 s in the kernel (`smul_time.log`, from `smul_time.lean`), and it takes 12.1 s inside a staged run (`smul_staged_q1z.log`). One fact would thus take about 6.5–6.8 h. |
| Values over `stageSize` (4·10⁶ nodes) in m31's `allPatternPairs` and `halfVectors`, which also recurse deeply in the `flatMap`/`flatten` path. | 1 | |
| Five formal-conjectures facts, `OEIS 111291 a 4`, `OEIS 358684 a 6`, `LatinSquare z 7`, `Wolstenholme 2124679` and `wowii103`. The first counts divisors over 10⁴ numbers in 32 staged filter chunks of about 280 s each, of which 18 finished in 5000 s. `LatinSquare z 7` goes through 5040 permutations by the `Fintype (Equiv.Perm (Fin 7))` instance chain and runs out of memory. `Wolstenholme 2124679` computes `C(4249357, 2124678)` on numbers of about 10⁷ bits, and `wowii103` is a `Finset.fold` over a graph. | 5 | |
| Two facts that ran out of time at 900 s while still progressing, trainverify `goal4Late_pm_filter_eq` and longfellow `v7Hash4_v1_compressed_bound` (`CMP[Rat]`). | 2 | See below. |

The cSHAKE gate count was also measured independently. No replacement was written for the nine minidregg facts
that recurse deeply, since the cost is the quadratic construction itself. The general fix for arrays built by
push is a tree-backed array representation in the copies (future work).

## Conversions with options only (no add-on), on library v13

`options_only_conversions.tsv` lists 48 facts by axiom name. For each fact it gives the smallest option set
that the controls allow, and the time and memory on library v13 itself, under a budget of 1500 s unless noted.
The same facts also prove on the build that has the extensions above, whose times are in the last two columns.

- csimp converts 9 facts: fc (7), goya (1) and the longfellow fact `OptimizedIOPCertificates_65`.
- stage converts 7: btc (2), zcash PostNu63 (3) and sounio (2).
- propSplit with split 16 alone, without stage or csimp (controls `c22n` and `lf22n`), converts 10: rimalloc (4),
  humanfia (2), trainverify (2) and the two longfellow facts `v7Hash{2,3}_v1_parameters` ax_1_6.
- csimp with propSplit and split 16 (control `lf22k`) converts 5 longfellow facts: `v7Sig`, `v8Sig`, `v7Hash4` and
  `v8Hash1` (each `_v1_parameters` ax_1_6), and `HahnRateSixteenth.construct` ax_1_7.
- stage, csimp and propSplit with split 16 together convert 1 fact, the humanfia fact `t7_a7_31`, which fails
  without staging.
- The same options with a shared staging module (`stage_native_axiom_nth` commands) convert 15 zcash facts.
- The same options with a budget of 3000 s convert 1 fact, the trainverify fact `goal4Late_pm_filter_eq` (1554 s
  and 6.6 GB on v13), which is one of the 80.

Two longer runs on that build (3000–5000 s) did not convert. The fc fact `OEIS 111291 a 4`
finished 18 of its 32 staged chunks in 5000 s, and longfellow's `v7Hash4_v1_compressed_bound` was stuck at an
`ite` after 3000 s.
