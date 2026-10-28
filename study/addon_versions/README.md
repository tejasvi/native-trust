# Add-on versions behind the paper's numbers

When an add-on changed after the runs that the paper cites, the version that produced those numbers is
kept here, byte-identical, in a directory named by the first 8 hex digits of its digest. The digest is
SHA-256 over the per-file SHA-256 lines of every file of the add-on's directory, sorted by path. From a
version's directory (or from the add-on's directory under `addons/`):

    find . -type f -printf '%P\n' | LC_ALL=C sort | xargs sha256sum | sha256sum

| digest | add-on | used by | the current version (`addons/`) |
|---|---|---|---|
| `ed02e2be…c566` | `bvs`, the kernel-checked route for `bv_decide` | the runs of Section 7: Table 8, all `bv_decide` facts of the corpus and the random sample (`study/results/bv_decide/`) | `addons/bvs/`: every file a module of Lean's module system, the drop-in tactic `bv_kdecide` and the command `bvs5_estimate` |

The digest of the archived copy is recomputed from its files (`results_index.tsv`, row RP12).
