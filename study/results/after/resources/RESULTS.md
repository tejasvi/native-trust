# Resource failures on library v8: final numbers (2026-10-24)

Scope: the 638 rows of `../library/shard_conversions.tsv` (TIMEOUT/ERROR facts of the study outside the
owner's smale6 package). Re-run on the adopted library v8 at the study budget, 900 s and 48 GB per fact.
Excluded from passes A and B:
- 117 `bv_decide` facts (veir 106, Radix 5, clean 3, Natuvea 2, asi 1; converted by the bv_decide route);
- the 99 clean facts proved by the earlier `@[kernel_fact]` remedy;
- the 16 longfellow shard conversions (V7Range0-7, V8Range0-7), whose result in the earlier pass stands;
- BerryEsseen's 8 uniform chunks, which went to pass C.

That leaves 398 facts in 16 packages (`lists/A_<pkg>.tsv`). Note: in `final_table.tsv`, column 12 is GB and
column 13 is seconds.

## Totals

- 398 re-run facts: 234 converted in passes A and B (A 179, B 55; the earlier pass 178), plus 8 in pass C = 242.
- BerryEsseen uniform chunks: 8 of 8 converted in pass C.
- Whole class of 638: 365 now have kernel proofs (242 + 8, the 16 longfellow nt3 shard conversions and the
  99 `@[kernel_fact]` facts). 117 are `bv_decide` (converted by the bv_decide route) and 156 still fail.
- No fact that the earlier pass proved fails on v8. mem_guard stopped none of my checks.

## Setup (reproducible)

- Library: `/home/ntbuild/nt_fix7/<tc>`, built from `nt_fix7/src`. The 16 source files are byte-identical to
  the library sources, NativeTrust/ (checked with sha256 lists). Toolchains v4.29.0-rc4 and v4.30.0
  were added with `ops/nt_fix7_build_resv8.sh` (copy of `nt_fix7_build.sh`; it refuses existing dirs and stubs
  CSimpCompat for 4.27-4.29). v4.33.0 and v4.34.0-rc1 were added for the iterator-string runs. All four builds exit 0.
- Driver: `python3 -I /home/ntbuild/m2_axioms5.py <name> <pkg> --skip-build --nt-root /home/ntbuild/nt_fix7
  --fact-timeout 900 --fact-mem 48 --include '^(?:<re.escape(axiom)>|...)$' --jobs J` (default `--split 8`).
  The regex is anchored because the driver uses `re.search`, and `ax_1_1` would also select `ax_1_14`.
  - Pass A: results `v8r-<pkg>`.
  - Pass B: the facts not PROVED in A, with `--extra-config 'propSplit := true'`, results `v8rp-<pkg>`.
  - The selected count matched the list for every package (driver line `outer_todo`, plus goya's one inner fact).
  - The exact argv of every run is in `records/sched_done/*.json` (`cmd`).
- Box lanes: a scheduler and a chainer (not in the artifact).
  - The scheduler keeps at most 6 slots, or 8 when MemAvailable > 350 GB at launch, and admits a job only
    if MemAvailable - 70 GB - headroom >= 48 GB per slot. Headroom = 48 GB x slots in use - RSS of my checks.
  - The chainer queues redo items for checks that mem_guard stopped (rc 143), then the pass-B item per package.
  - mem_guard stopped none of my checks (0 log lines on 10-24). There were no rc 143 results and no chainer
    flags.
- Pass C pools:
  - shard pool v4: a copy of the earlier pool, with the job-line fix below.
  - shard pool v5: v4 plus piece-count discovery. Piece 0 prints `SHARD 0/P`; only pieces
    1..P-1 run, and the combine imports pieces 0..P-1.
  - Piece modules are named `F2sh_<tag>_<k>` so that mem_guard covers them. Budget 900 s, 48 GB per piece.

## Passes A and B (398 facts)

| package | facts | earlier pass | A conv/att | A s (proved) | A GB (proved) | B conv/att | B s (proved) | B GB (proved) | total |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| s_zcash_ironwood | 191 | 154 | 131 / 191 | 2-272 | 2.9-42.5 | 49 / 60 | 9-199 | 3.2-31.0 | 180 |
| s_emberian_minidregg | 85 | 13 | 22 / 85 | 1-695 | 1.5-42.9 | 0 / 63 | - | - | 22 |
| longfellow-zk | 46 | 0 | 6 / 46 | 51-287 | 10.3-42.2 | 0 / 40 | - | - | 6 |
| formal-conjectures | 21 | 0 | 3 / 21 | 201-213 | 32.0-37.5 | 0 / 18 | - | - | 3 |
| trainverify | 13 | 1 | 5 / 13 | 2-262 | 3.3-42.4 | 0 / 8 | - | - | 5 |
| s_Provenance_Works_Radix | 11 | 10 | 10 / 11 | 1-2 | 1.8-2.1 | 0 / 1 | - | - | 10 |
| sounio | 6 | 0 | 0 / 6 | - | - | 0 / 6 | - | - | 0 |
| aks | 5 | 0 | 0 / 5 | - | - | 0 / 5 | - | - | 0 |
| sorting-network-expanders | 5 | 0 | 0 / 5 | - | - | 0 / 5 | - | - | 0 |
| humanfia-icho2026 | 4 | 0 | 1 / 4 | 266 | 41.1 | 2 / 3 | 19-266 | 9.3-32.0 | 3 |
| s_moggedhedien_rimalloc_verify | 4 | 0 | 0 / 4 | - | - | 4 / 4 | 61-670 | 2.8-14.7 | 4 |
| s_Rob1Ham_btc_lean_spec_proofs | 3 | 0 | 0 / 3 | - | - | 0 / 3 | - | - | 0 |
| rs-mca-m31_flatness_keystone | 1 | 0 | 0 / 1 | - | - | 0 / 1 | - | - | 0 |
| s_BobDyLean_bobdylean_paper_artifact | 1 | 0 | 0 / 1 | - | - | 0 / 1 | - | - | 0 |
| s_clementefalcone_goya_ledger_formal | 1 | 0 | 0 / 1 | - | - | 0 / 1 | - | - | 0 |
| s_leanprover_community_physlib | 1 | 0 | 1 / 1 | 213 | 40.1 | - | - | - | 1 |
| **total** | **398** | **178** | **179 / 398** | 1-695 | 1.5-42.9 | **55 / 219** | 9-670 | 2.8-32.0 | **234** |

- Every conversion of the earlier pass is reproduced. All 149 T0 facts were converted in A, and the 29 T2 facts (witness
  not-and) in B. No red flags.
- New conversions over the earlier pass: 56. The difference comes from the larger budget (900 s and 48 GB, against
  300 s and 22-24 GB).
  - In A: 30 (zcash 6, minidregg 9, longfellow 6, fc 3, trainverify 4, humanfia 1, physlib 1).
  - In B: 26 (zcash 20, of them 10 `¬ MsmMatch` sweep facts on which the earlier pass's witness had run out of memory;
    rimalloc 4; humanfia 2).
- Failures: ERROR memory at 42.2-46.1 GB maxrss (the 48 GB cap), after 133-730 s. TIMEOUT at 900 s.
  FAILED: kernel deep recursion, blocked constants, or `Nat.Prime`.
- Per-fact data: `facts_AB_final.tsv`. Summary: `summary_AB_final.md` (also groups the remaining failures by
  shape). Driver results: `fetched/v8r-*.ax.tsv`, `fetched/v8rp-*.ax.tsv`.

## Pass C: shards (900 s, 48 GB per piece)

| fact | N | pieces P | CPU-s total | max per piece | combine | verdict |
|---|---:|---:|---:|---:|---:|---|
| BerryEsseen uniform Chunk0 | 2^40 | 176 | 13,222 | 351 s, 38.6 GB | 13 s | PROVED |
| Chunk1 | 2^40 | 176 | 12,935 | 38.9 GB | 13 s | PROVED |
| Chunk2 | 2^40 | 176 | 13,290 | 370 s, 39.6 GB | 13 s | PROVED |
| Chunk3 | 2^40 | 176 | 13,399 | 42.4 GB | 16 s | PROVED |
| Chunk4 | 2^40 | 176 | 12,158 | 44.7 GB | 13 s | PROVED |
| Chunk5 | 2^40 | 176 | 11,186 | 44.8 GB | 13 s | PROVED |
| Chunk6 | 2^40 | 176 | 11,255 | 44.6 GB | 14 s | PROVED |
| Chunk7 | 2^40 | 176 | 11,116 | 44.3 GB | 13 s | PROVED |
| longfellow `v7Hash1_v1_parameters` ax_1_10 (B: TIMEOUT after 7 of 8 pieces) | 32 | 32 | 2,952 | 33.5 GB | 2 s | PROVED |
| longfellow `HahnRateSixteenth.allRowsBool` (B: TIMEOUT) | 32 | 21 | 6,029 | 296 s, 44.6 GB | 2 s | PROVED |
| trainverify `goal3_public_contract_joint_witness` ax_1_2 (B: TIMEOUT after 5 pieces) | 2^20 | 5,943 | 11,321 | 4.1 GB | 6 s | PROVED |
| longfellow `HahnRateSixteenth.valid2109/2119/2129/2140/2152` (B: memory; N=32 pieces died at 47 GB) | 2^20 | 641 each | 13,335 / 11,068 / 8,440 / 6,937 / 5,791 | 21 s, 5.4 GB | 1.2-1.3 s | 5 x PROVED |

The uniform chunks need no string add-on: the Uniform modules contain no `String`.

Did not convert in pass C:
- longfellow `v7Hash4_v1_parameters` and `v8Hash1_v1_parameters` ax_1_10. With N = 32 or 256, the pieces from
  52% of the index range onward die at 46 GB after ~250 s, the same at both granularities.
- btc `merkle_matrix_64`. Piece memory grows ~2.4 GB per piece index; pieces 16+ die at 44 GB.
- aks `ProfileInvolution` (P = 8). Pieces 3, 5 and 6 are atomic conjuncts that die at 46 GB.
- minidregg `official_hash_vectors` (P = 35). One KAT piece dies at 44.9 GB.
- fc Idoneal ax_1_63/64/65. Piece 0 dies at 45 GB before any piece is written.
- minidregg `reach_certified`. Shard mode fails: the statement uses the nested native fact `graph_built`
  ("unknown constant _ktshard...graph_built._kernel...").

## Issues found (defense-side tooling)

1. The earlier shard pool writes job lines `"$TAG $PKG $k $N $XLP"`. With an empty EXTRA_LP the line
   ends in a blank, and `xargs -L 1` then joins it with the next line. All lines become one command, so each pool
   runs only its first piece. Seen here as pools that ended after ~6 s; fixed in pools v4 and v5.
2. Shard count on right-nested `&&` chains. The split gives `a` half the budget and `b` the rest, so the k-th
   conjunct of a chain gets N/2^k. With N = 64 the BerryEsseen chunk got only P = 21 pieces, and the last one
   held the 29-cell tail; it died at 45.7 GB, and the combine failed. N = 2^40 gives one piece per conjunct
   (176 pieces). Per-piece processes then pay ~3-14 s of setup each (141 of the 176 pieces are cheap).
   `List.all` tables split by index and do not have this problem.

## Still failing (164 of 398 after A and B; 156 after pass C, which converted 8 of them)

By likely cost driver (shapes from final_table column 8; per package and shape in `summary_AB_final.md`):
- **Large computed values, no structure (80).**
  - minidregg 63: `EQ[Option]` 44 and 19 other checks; 9 of them are FAILED with "(kernel) deep recursion"
    inside hash computations (cSHAKE/Keccak).
  - zcash `EQ`/`NE[G]` 4; fc `EQ[Nat]` 7 and `EQ[List]` 1; sounio `EQ[Nat]` 2; m31 1; trainverify `EQ[List]` 1;
    longfellow `CMP[Rat]` 1.
  - They die at 42-46 GB or by TIMEOUT. Kernel memory grows inside one declaration, so they need staged
    evaluation (the csimp work).
- **Deep unary recursion (21, longfellow).** Row.Valid/Sharp, `prop:other`, `CMP[Rat]`, DirectClique: FAILED
  with "(kernel) deep recursion detected". They need `@[kernel_replace]` closed forms.
- **Conjunctions, tables and other shapes (56; pass C converted 8, so 48 remain).** A single piece exceeds
  48 GB, or the memory runs out in the first piece:
  - aks and sorting `checkCertificateB128`/`checkInvolutionSpec`: 10.
  - zcash `MsmMatch>AND`: 4 (the `List.Perm` conjunct).
  - btc: 3 (`bytesBEq` and the merkle matrix).
  - longfellow 18: `ite` 8; HahnDelsarte `certificateValid` tables 5 (all converted in pass C);
    integratedLocalValid 3 (pass C converted lf32; lf106/lf130 do not); DirectClique 1; `allRowsBool` 1
    (converted in pass C).
  - trainverify 7: `AND` 4; `prop:other` 2; the joint-witness `List.all` 1 (converted in pass C).
  - fc 7: `AND` 2, Idoneal `¬∃` 3, `∀ x ∈` 1, `¬∃` 1.
  - humanfia `AND` 1; BobDyLean `AND` 1; Radix `FORALL[Word11^2]` 1; sounio `subBPlus`/`conflictBPlus` 4
    (closure saturation).
- **Blocked (3).** zcash `EQ[Prod]` 2 and `PinnedConstraintSystem` 1: FAILED blocked in 225-409 s.
- **Primes (4).** fc `Nat.Prime` 3 and goya 1. The kernel does not reduce the `Nat.Prime` decision for
  10-digit primes; they need `@[kernel_fact]` certificates.

## Files

In this artifact: this report and `facts_AB_final.tsv` (one line per re-run fact: shape, verdicts and resources of
passes A and B) in this directory; the driver results `v8r-<pkg>` and `v8rp-<pkg>` in `../library/runs/`; the combine logs
of the shards in `../library/shards/`.
