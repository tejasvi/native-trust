# BerryEsseen parse-once add-on

Kernel proofs for BerryEsseen's large cover facts. Each such fact, `coverStringAccepted* … data = true`, decides a
certificate stored as a string literal (up to 1.2 MB). The tokenizer add-on in `../berryesseen/` splits a fact into
pieces, but every piece parses the whole string again. This add-on parses each certificate once and checks the pieces
against the parsed tree. It converts the 259 cover facts that the tokenizer add-on did not convert: the 61
`Small.Data.Cover*` facts, 197 `Covers.Data.DW*` facts and `Covers.Data.BE223`.

For a fact `F` about the string `D`, with `P` the prefix of the new declarations:

1. `bo_tree P D` runs compiled code that reads `D` and adds one definition per node of the cover tree (`P.t_<i>`, in
   preorder), in the shape that the package's parser produces. It also adds the character list `P.c_<j>` of each
   literal piece of `D`.
2. `bo_parse P F` adds the declaration `P.hpL : parseCoverL 64 (tokensL (P.c_1 ++ …)) = some (P.t_0, [])`, which the
   kernel checks by evaluation; this is the only evaluation of the parser. It then adds `P.parse`, which turns `F` into
   a check of the tree `P.t_0`.
3. `bo_leaves P F a b` adds one declaration `P.leaf_<i>` for every leaf with `a ≤ i < b`. The kernel proves these by
   evaluation, without the string.
4. `bo_assemble P F` adds a declaration `P.node_<i>` for every split node, with the test of its split point (two
   rational comparisons), and then `P.final`, which has the statement of `F`. The generated module tags `P.final` with
   `@[kernel_fact]`, so NativeTrust's check of the fact reports `PROVED`.

The compiled code only proposes the tree: the tree is a definition, and `P.hpL` checks it against the package's
parser. Every final theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Files

| path | contents |
|---|---|
| `BoCore.lean` | the lemmas, the certificate reader and the four commands; imports `NativeTrust` and `BeList` from `../berryesseen/` (which imports `StrRepl`, `StrReplace` and `SplitOnSpace` from there) |
| `gen/<tag>/` | the modules of each of the 259 facts, as they were run: `BO_<tag>_Tree`, `BO_<tag>_Parse`, the leaf modules `BO_<tag>_L<j>` (listed in `batches.txt`), `BO_<tag>_All` (the assembly and the `@[kernel_fact]` tag) and `F2_<tag>` (NativeTrust's check of the fact) |
| `scripts/gen_cover.py` | writes the modules of one fact |
| `scripts/leaves.tsv` | the number of leaves, characters and tokens of each cover module of the package |
| `scripts/run_cover3.sh`, `scripts/lrun3.sh` | build the modules of one fact in order (Tree; Parse and the leaf modules in parallel; All; F2) in the study machine's layout |
| `scripts/chk_bo.sh` | exports theorems with their closure (lean4export) and checks the export with nanoda and con-ron |
| `scripts/export_axtsv.py`, `scripts/results_md.py`, `scripts/summary.py` | build the result tables from the build logs |

Tags: `C3` to `C6` for `Small.Data.Cover3` to `Cover6`, `S<n>` for the other `Small.Data.Cover<n>`, `D<n>` for
`Covers.Data.DW<n>`, and `B223` for `Covers.Data.BE223`.

The results are in `study/results/after/specific/covers/`. That directory holds NativeTrust's check of each fact
(`<tag>/F2_<tag>.log`), the per-fact table `berry-esseen-covers.ax.tsv`, the per-cover table `RESULTS_covers.md` and
the logs of the independent checks (`checks/`).

## Build

Everything uses toolchain `leanprover/lean4:v4.34.0-rc2`, the version pinned by the package.

1. Build NativeTrust library v8, the library used for these runs, from the sources in
   `study/library_versions/9011ea48/`: set its `lean-toolchain` to the toolchain above and run `lake build` (as
   `study/builds/nt_fix7_build.sh` does).
2. Build BerryEsseen at commit `bfb22608ad18b4fa9fda8dd9a1ed2c2b6fbc29e7` with `lake exe cache get` and then
   `lake build`.
3. Build the add-on. Set

       LEAN_PATH=<v8>/.lake/build/lib/lean:<build>:<BerryEsseen's LEAN_PATH>

   where `<build>` is a new directory for the add-on's `.olean` files and BerryEsseen's LEAN_PATH is the output of
   `lake env printenv LEAN_PATH` in the package. Compile `StrRepl`, `StrReplace`, `SplitOnSpace` and `BeList` from
   `../berryesseen/`, and then `BoCore`. Use `lean -j1 --tstack=1048576 -o <build>/X.olean X.lean` with
   `LEAN_NUM_THREADS=1` for every module; none takes more than 2 s.

## Check one fact

`Small.Data.Cover21` (tag `S21`, 40 leaves) takes about an hour of CPU time. Add `gen/S21` to LEAN_PATH, and in
`gen/S21/` compile each module with `lean -j1 --tstack=1048576 -o X.olean X.lean`, in this order:

| module | time | peak memory |
|---|---|---|
| `BO_S21_Tree` | about 1 s | |
| `BO_S21_Parse` | about 3 s (the parse: 2.3 s) | 2.0 GiB |
| `BO_S21_L0` to `BO_S21_L3` (12, 12, 12 and 4 leaves; independent of each other) | about 90 s per leaf | 12.6 GiB |
| `BO_S21_All` | 1 to 3 s | |

Then run `lean F2_S21.lean` without `-o` (about 1 s). Its output has the line `PROVED` for the fact, and
`BerryOpt.S21.final` appears in its error output. The whole fact took 3,539 CPU-s.

`scripts/run_cover3.sh` does the same in the study machine's layout under `${NT_BOX}`. There, the toolchains are in
`elan/` and library v8's build is in `nt_fix7/v4.34.0-rc2/`. The directory `work_parse_once/` holds the add-on's
builds in `lib3/` and the modules in `covers/<tag>/`; its `scripts/` holds these scripts and `pkg_lean_path.txt`, which
contains BerryEsseen's LEAN_PATH. `SLOTS` lists the slots that may be used (for example `SLOTS="0 1 2 3"`), and each
slot runs one lean process.

## Regenerate

    python3 scripts/gen_cover.py TAG MODULE LEAVES BATCH OUTDIR

for example `python3 scripts/gen_cover.py S21 BerryEsseen.Upper0423.Small.Data.Cover21 40 12 gen/S21`. LEAVES is
column 1 of `scripts/leaves.tsv` in the row whose column 4 is the module without `BerryEsseen.Upper0423.`. BATCH is the
number of leaves per leaf module: 20 for Cover3 to Cover6 and for `n ≤ 16`, 12 for `17 ≤ n ≤ 63`, and 6 for `n ≥ 64`,
where `n` is the number in the module's name. With these values the script reproduces every file under `gen/` byte
for byte.

## Cost

The 259 facts have 13,495 leaves. Their conversion took 479.5 CPU-h, the sum of the elapsed times of all their lean
processes (tree, parse, leaf modules, assembly and final check); each process ran on one thread. The total includes the
reruns after two outages of the machine and after one leaf module reached its 24 GiB address-space cap. The largest
process used 42.4 GiB.

| family | facts | leaves | CPU-h | largest process |
|---|---:|---:|---:|---:|
| `Small.Data.Cover*` | 61 | 5,022 | 95.4 | 26.8 GiB (the parse of Cover3) |
| `Covers.Data.DW*` | 197 | 8,450 | 383.0 | 40.8 GiB |
| `Covers.Data.BE223` | 1 | 23 | 1.1 | 42.4 GiB |

## Independent checks

lean4export (v4.34.0-rc2) exported each theorem below with its closure, and nanoda and con-ron (as shipped with
v4.35.0) checked the export (`scripts/chk_bo.sh`). Both checkers permitted only `propext`, `Classical.choice` and
`Quot.sound`.

| export | nanoda | con-ron |
|---|---|---|
| `BerryOpt.C6.final` (Cover6, the whole fact: 192 leaves) | 7,635 declarations, no errors (13,269 s) | not run |
| `BerryOpt.S17.final` (Cover17: 44 leaves) | 7,043 declarations, no errors (6,007 s) | not run |
| `BerryOpt.D5.final` (DW5: 21 leaves) | 6,952 declarations, no errors (1,176 s) | not run |
| `BerryOpt.D67.final` (DW67: 38 leaves) | 7,020 declarations, no errors (12,627 s) | not run |
| `BerryOpt.D200.final` (DW200: 46 leaves) | 7,052 declarations, no errors (13,560 s) | not run |
| `BerryOpt.BE3.final` (BE3 by this method, 1 leaf; module `checks/K_BE3.lean`) | 6,869 declarations, no errors (65 s) | 6,396 declarations accepted |
| `BerryOpt.D5.node_7` (a split node with 2 leaves) | 2,392 declarations, no errors | 2,145 declarations accepted |
| `BerryOpt.C5.node_7` (a split node with 2 leaves) | 2,392 declarations, no errors | 2,145 declarations accepted |
| `BerryOpt.C5.parse` and `BerryOpt.C5.node_7` (two string literals, the parse, a split node) | 7,413 declarations, no errors | stopped by its own limit before checking: "fuel exhausted" at the 100,000-element character list `BerryOpt.C5.c_1` |

con-ron was run only on the smaller exports. Each nanoda log also reports one error from nanoda's pretty printer
("Unable to print axioms"), which is not a result of type checking. The logs are in
`study/results/after/specific/covers/checks/`.
