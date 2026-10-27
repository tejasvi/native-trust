# minidregg add-on (C4 linearization)

This add-on contains code from emberian/minidregg and is licensed under the GNU Affero General Public
License v3.0 or later; see LICENSE. The rest of the artifact keeps its licenses.

A proved replacement that lets NativeTrust convert the facts of `Compiler.ObjectiveBendC4Vectors`.
They run `Minidregg.Compiler.ObjectiveBendC4.linearize` on precedence graphs (pommette's published
vectors, refusals, fuel cases, random DAGs). `linearize` counts the members of precedence lists in a
`Std.HashMap String Int` and indexes the suffix tail in a `Std.HashMap String Nat`. `String.hash` has no
kernel definition, so on v13 these facts are blocked on `String.hash` and `System.Platform.getNumBits`.
The add-on uses toolchain `v4.30.0`, the version the package pins; the module imports `NativeTrust` and
`Compiler.ObjectiveBendC4Vectors`.

| file | contents |
|---|---|
| `NTMinidreggC4.lean` | everything below; the three theorems depend only on `propext`, `Classical.choice` and `Quot.sound` |

- `linearize_eq` (`@[kernel_replace_retry]`): `linearize = linearizeL`, where `linearizeL` is the same code
  over association lists (`lookup`; `insert` is `cons`), and `removeSuffixTailAndReverseL` likewise for the
  auxiliary function. `linearize` reads its maps only through `getD`, `get?` and `contains` and writes them only with
  `insert`, so the hash function does not matter.
- The proof is a simulation. Every hash map the original builds is `toHM l` for the list `l` the copy
  builds (`toHM` inserts a list's entries into `∅`, so `toHM (linsert l k v) = (toHM l).insert k v` by
  `rfl`). `getD`, `get?` and `contains` of `toHM l` are the list lookups (by core's `getElem?_insert`). Each
  `for` loop of the original is the copy's loop with the state mapped (by `forIn_sim` and `bind_sim`), and the
  copy's matchers on map-free types are the original's (by `rfl`).
- The proof follows the elaborated `do` code of the package's current `linearize`; a change to that
  function needs a matching change here.
- `table_eq`, `expected_eq` (`@[kernel_replace_retry]`): the vector file's `table` and `expected` as
  literal lists. Both are parsed from string literals with `String.splitOn`, which the kernel evaluates
  slowly (about 370 s for the first 7 lines of `expected`, 22 s for `table`), and a structured check
  re-parses them in every piece. The equations are proved with `kdecide` once, when the add-on is compiled;
  this takes 96 s and 12.3 GB.

To use the add-on, compile `NTMinidreggC4.lean` to an olean in the package's environment under a 24 GB
address-space cap, then run the driver with `--extra-path <this directory> --extra-import NTMinidreggC4`.

On an earlier build with the word-size case split, in the driver runs `v8s-r4-md-c4-a2` and
`v8s-r4-md-c4-4000-m120`, all 5 facts are PROVED, with 0 accessibility-generator fallbacks. With 3 facts
run in parallel, each under a 32 GB cap, `pommette_vectors` takes 445 s and 10.3 GB, `pommette_refusals`
takes 48 s, and `fuel_is_not_inconsistency` and `dag_local_orders` take 1 s each.
`ordered_presentation_invariance_4000` checks 4,000 random DAGs in one kernel check, about 0.13 s and 27 MB per
DAG; it takes 659 s and 93.6 GB under a 120-GB cap and ends with ERROR memory under 32 GB.
With the add-on imported, the minidregg gate set stays 12/12 PROVED.
On the later build with the word-size case split, with the same add-on file compiled again, the 4 facts within
900 s are PROVED again in the driver run `v8s-r4b3-md-c4-p13c`. `ordered_presentation_invariance_4000` was run
only on the earlier build, since it needs about 94 GB.
