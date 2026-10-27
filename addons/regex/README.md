# lean-regex add-on

Proved replacements that let NativeTrust convert lean-regex's two case-fold table facts,
`checkAllPairs_isLtFirst_caseFoldRepresentatives` and `checkAllPairs_noChain_caseFoldRepresentatives`
(`RegexCorrectness.Unicode.CaseFold.Data`). Each decides `checkAllPairs (p caseFoldRepresentatives.get)`:
2.3M pair checks over the 1,512-row table, each reading an `Array` (a list in the kernel), after parsing the
table from a 15.7 KB `include_str` with the legacy `String.splitOn`. On v13 alone they run out of memory
at 37.8 GB. The add-on uses toolchain `v4.34.0-rc1`, the version the package pins; the module imports
`NativeTrust` and the package's `RegexCorrectness.Unicode.CaseFold.Data`.

| file | contents |
|---|---|
| `NTRegexCaseFold.lean` | all of the below; every theorem depends only on `propext`, `Classical.choice` and `Quot.sound` |

- `splitOn_eq_splitOnL` (`@[kernel_replace_retry]`): `String.splitOn` is `List.splitOn` on `toListFast` for a
  one-character separator, and core's algorithm otherwise. The proof is `splitOn_singleton` from the
  BerryEsseen add-on's `SplitOnSpace.lean`; it needs core ≥ 4.34.
- `sortedPat_eq`, `noChainPat_eq` (`@[kernel_fold]` patterns + `@[kernel_replace_retry]`):
  - `checkAllPairs (isLtFirst arr)` is the O(n) check of adjacent pairs (`sortedFast`);
  - `checkAllPairs (noChain arr)` is an O(n) test of the second components against a bit set of the
    first components held in one `Nat` (`noChainFast`, GMP `lor`/`shiftLeft`/`testBit`).
  Both are proved for every array.
- Under the `module` system, the package's definitions are private to its module, and a `module` cannot
  import NativeTrust. So the add-on is a plain file. It aliases the private constants with `run_meta` and
  `addDecl`, so the aliases are the same kernel constants. It proves its verbatim copy of `checkAllPairs`
  equal to the original by kernel `rfl`, and it builds the fold patterns from the private constants as
  they occur in the decided terms.

To use the add-on, compile `NTRegexCaseFold.lean` to an olean in the package's environment, that is, run
`lean -o` with `LEAN_PATH` set to the NativeTrust build for v4.34.0-rc1, the package's `lake env` path and
this directory. Then run the driver with `--extra-path <this directory> --extra-import NTRegexCaseFold`.

These are the results on library v13 with the iterator-strings patch of v14, in the driver run `v8s-r4-regex-f1`:
- Both facts are PROVED in the retry, each in 219-220 s and 28.9 GB. The parse takes most of that time,
  about 60 ms and 19 MB per table line, in `trimAscii` and `String.foldl`.
- The axioms read back from the olean are the standard three. nanoda checked the export (6,440
  declarations) without errors, and it rejects the control, the native original of
  `checkAllPairs_noChain_caseFoldRepresentatives`.
- con-ron declines the `.eval` theorem with "arena: expr constructor at capacity"; the attempt takes 50 s
  and 26 GB under a 100 GB cap. That is a capacity limit of the checker, not a rejection, and it has no
  option to raise it.

On the build with the word-size case split, both facts are PROVED again in the driver run `v8s-r4b3-regex-p13c`.
