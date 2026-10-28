# NativeTrust: kernel-checked replacements for `native_decide`

`native_decide` proves a decidable proposition by running compiled code. Since Lean 4.29 every use
adds an axiom `<decl>._native.native_decide.ax_N : decide p = true`, so the result trusts the
compiler, the interpreter and every `@[implemented_by]`/`@[extern]` implementation it reaches.
Mathlib, `lake check`, Comparator and the independent proof checkers refuse such axioms.

For the same statements, NativeTrust produces proofs that Lean's kernel checks by evaluation and that
depend only on `propext`, `Classical.choice` and `Quot.sound`. Their trusted base is Lean's kernel,
including its built-in arithmetic on natural numbers. It works on existing projects without editing
them, names the constant that blocks a fact when there is one, and offers two ways to remove
unnecessary `native_decide` from a project for good.

NativeTrust depends only on core Lean and works in Mathlib projects. The toolchain is
`leanprover/lean4:v4.35.0-rc3`. The library builds on Lean 4.27 to 4.35 and on recent nightlies (on
4.27-4.29 without the `String` replacements of `NativeTrust.StrLib` and without the `csimp` option,
both of which need Lean 4.30 or later).

## Installation

Add the package to the project's `lakefile.toml`:

```toml
[[require]]
name = "native_trust"
git = "https://github.com/tejasvi/native-trust"
rev = "v1.0.1"
```

In a `lakefile.lean`, write `require native_trust from git "https://github.com/tejasvi/native-trust" @ "v1.0.1"`.
Then run `lake update native_trust`. The repository also holds the study's data, about 140 MiB, but
`lake build` builds only the NativeTrust modules that your project imports. On Lean
4.27-4.29, copy `NativeTrust/StrLibStub.lean.txt` over `NativeTrust/StrLib.lean` and
`NativeTrust/CSimpCompatStub.lean.txt` over `NativeTrust/CSimpCompat.lean` in
`.lake/packages/native_trust` before building. The build prints about 30 warnings from NativeTrust's own
sources, mostly deprecated names such as `Lean.levelZero`; they do not affect the results.

## Quick start: switch a project with one import

In the packages we studied, nearly every fact that NativeTrust converted never needed compiled
evaluation: of 52,821 native facts in 16 public packages, plain kernel evaluation (what
`decide +kernel` does) proved 51,307 of the 51,329 converted facts that we re-ran. So the first step is one line in a module that your `native_decide` modules
import:

```lean
import NativeTrust.KernelFirst
```

Every `native_decide` and `decide +native` then tries `decide +kernel` first, within
`nativeTrust.kernelHeartbeats` (default 2000, in thousands like `maxHeartbeats`). It falls back to
Lean's own native path only when the kernel does not prove the goal, and says why in an info message.
- `#kernel_first_summary` lists the calls in a file.
- `set_option nativeTrust.kernelFirst false` switches it off.

On unmodified sources, the native axioms of lido-srv3 (723 modules) went from 70 to 0, and those of
cvc5/logos's 10 largest modules from 1,043 to 0, with build time within 2% (343 → 345 s and
187.6 → 184.7 s). Build time rises where kernel checks are expensive: codegraff, a small package from a
random sample, took 17 s instead of 2.6 s.

Like any import of `Lean`, Batteries, Aesop or Mathlib, the module brings `Lean` and `Std` into scope
in every module that imports it, and their instances can change how other code elaborates. In one of
24 sampled packages, six structure literals in the shorthand `{ a, b }` whose expected type was not
yet known became set notation through `Std`'s generic `Insert` and `Singleton` instances. Each can be fixed
with a type ascription, `({ a, b } : Cell)`, or with explicit fields.

`import NativeTrust.KernelFirstLite` provides the same switch, implemented as two macros that import
nothing beyond `Init`, so nothing else changes. It has no options, does not say why it falls back and
has no `#kernel_first_summary`. Its budget is fixed at 2000. Because it lacks the static triage, a call
that the kernel cannot check spends that budget before it falls back, so lido-srv3 took 421 s instead
of 360 s.

To keep new code clean, `set_option linter.nativeTrust true` warns at each `native_decide` whose goal
`decide +kernel` proves, with a "Try this: decide +kernel" fix, and warns when a native fact can
never be checked by the kernel, naming the blocking constant.
- `linter.nativeTrust.strict` makes the first warning an error, for CI.
- `#native_decide_audit` prints a verdict for every native fact in a module.

To remove `native_decide` from the sources, `lake exe ntrust migrate` rewrites to `decide +kernel`
every use whose facts the kernel checks, and verifies the build (below). For facts that the kernel
cannot check by plain evaluation, use the tools below.

## Usage

```lean
import NativeTrust

-- 1. Drop-in replacement for `native_decide`
theorem t : (List.range 300).reverse.mergeSort = List.range 300 := by kdecide
#print axioms t   -- [propext, Quot.sound]

-- 2. Re-prove an existing native_decide theorem (from any imported module) without touching it
kernelize MM4.c3_d3_c0               -- adds `MM4.c3_d3_c0.kernel`, same statement
kernelize foo as foo_k (config := { split := 8 })

-- 3. Every native_decide theorem of an imported module (one OK/FAIL line per theorem)
kernelize_module MM4.N3.c3_c0

-- 4. Triage without evaluating: can the kernel evaluate the native facts behind `T`?
#kernel_blockers T
#kernel_blockers_const myChecker      -- the same for a checker function, no theorem needed

-- 5. Proof-carrying replacement: evaluate with `g`, bridged back to `f` by congruence
@[kernel_replace] theorem f_eq_g : @f = @g := …   -- e.g. a fuel version, or a kernel-form checker

-- 6. A replacement used only in a retry, after the first attempt fails; `@[kernel_fold]` lets it
--    target one instance of a function with type-class arguments (the fold is definitional)
@[kernel_fold] def F (s pat r : String) : String := s.replace pat r   -- `String` patterns only
@[kernel_replace_retry] theorem F_eq : @F = @G := …

-- 7. A function that reads its last (String) argument only through `String.toList`: applied to a
--    long literal, NativeTrust evaluates `g … s.toList` and never builds the string
@[kernel_string_arg] theorem f_eq : ∀ x s, f x s = g x s.toList := …

-- 8. Use this proof for every native fact `decide P = true` (e.g. primality certificates)
@[kernel_fact] theorem h : P := …

-- 9. Admission check (registries, benchmark harnesses): CLEAN, KERNELIZED (adds T.kernel) or
--    REJECTED with the reason (another non-standard axiom, or the limitation that blocks it)
trust_check T
```

For drivers that process whole projects one fact per process, the listing commands address facts
and theorems by index within a module, so private theorems and the private axiom names of
module-system files are reachable too:

```lean
#native_axioms M                  -- AX <axiom> <tactic> <inner> <i>: every native axiom declared in M
prove_native_axiom_nth M i        -- PROVED/FAILED; the proof is registered, so modules importing
                                  -- this one (compiled with `lean -o`) reuse it
#native_theorems M                -- THM <theorem> <direct facts> <all facts> <i>
trust_check_nth M i               -- trust_check on the i-th theorem listed
#kernel_blockers_nth M i
stage_native_axiom_nth M i        -- STAGED: proves the values of the data the i-th fact reaches and
                                  -- registers them, so facts in modules importing this one reuse them
set_option nativeTrust.eprint true   -- also write reports to standard error at once (kept when a
                                     -- time or memory limit stops the process later)
```

### Whole projects

Run in the root of a Lake project that depends on NativeTrust:

```
lake exe ntrust --jobs 8          # options: --fact-timeout S --fact-mem GiB --split K --out DIR
                                  #          --skip-build --nt-lib DIR --modules A,B
```

It proves every native fact in its own process, under a time and memory limit. Facts used inside
definitions and instances are proved first and reused. It writes `.ntrust/report.tsv` (one line per
fact, with the verdict and the blocking constants), `.ntrust/Kernel/` (a kernel supplement with a
`T.kernel` theorem for every theorem `T` whose facts were all converted, in each module that uses a
native tactic), `.ntrust/theorems.tsv` and
`.ntrust/comparator.json` (each original theorem paired with its kernel version). Exit code 0 means
everything converted. `ADOPTING.md` is a guide for projects and includes a CI recipe.

```
lake exe ntrust migrate [--report FILE] [--fact-budget HB] [--max-slowdown F] [--dry-run] [--jobs N]
                        [--rounds N] [--round-timeout S] [--build-mem GiB] [--restore] …
                        (lake exe ntrust migrate --help)
```

`migrate` rewrites the sources in place. A `native_decide` or `decide +native` becomes
`decide +kernel` only if plain kernel evaluation proves every fact behind it within a per-fact budget
(`--fact-budget`, default 2000, the switch's default), so expensive facts stay native. It rebuilds the
project and reverts rewrites that fail, that exceed a time limit per module, or that make a module's
build more than twice as slow (`--max-slowdown`, default 2). Then it checks the remaining axioms, and
it keeps the originals for `--restore`. On a random sample of 24 packages with 1,472 native axioms,
the defaults removed 30% of them (median 25% per package), and no package's build took more than 1.7
times as long (the slowest went from 1.03 to 1.74 s). Without the budget and the slowdown limit (`--fact-budget 0 --max-slowdown 0`) it
removed 54% (median 76%), but build time rose by a median factor of 1.9, and by up to 143.5 times where
single facts are expensive in the kernel. In both runs 23 packages built afterwards, and the 24th
failed only in its own checks that require certain theorems to keep a native axiom. AXLE offers the
same rewrite, inside one file, as one of its repairs.

### Options

Options are set with `kdecide (config := { ... })`. `kernelize` and the driver's `--extra-config` take
the same fields.

| option | default | meaning |
|---|---|---|
| `split` | 1 | check in up to this many kernel declarations, split along `&&` and along `List.all l f`; each declaration has its own kernel caches, so this bounds memory |
| `quickHeartbeats` | 2000 | try the whole term in the kernel once within this budget (thousands) before any search for structure; cheap facts are proved as they stand |
| `searchHeartbeats` | 5000 | budget of each meta-level search for structure (where to split, which conjunct); giving up is safe, the term is then checked whole |
| `witness` | true | check `List.any`, `∃ x < n` and `∃ x ∈ l` at the witness that compiled code proposes |
| `propSplit` | false | structured checks: `∧` split into declarations, `¬ (A ∧ B)` and `A ∨ B` checked at the part that compiled code names, bounded `∀` as `List.all`; for facts that fail for resources |
| `shards` / `shardOnly` | 0 | prove piece `k` of `N` in its own module (`shardOnly := k+1`), then combine the imported pieces (`shards := N`) |
| `stage` | false | staged evaluation: when the whole term does not check within `quickHeartbeats`, compiled code computes its expensive closed parts, each `part = value` is proved by kernel evaluation in its own declaration, and the fact is evaluated over the proved values; `stageHeartbeats`, `stageMax`, `stageSize`, `stageDepth`, `stageSubterms` and `stageGlobal` bound and steer it |
| `csimp` | false | use the `@[csimp]` equations of Mathlib and of the project (not of core) as kernel replacements, for example `Nat.choose = fast_choose` and trial division up to the least factor for primality |
| `maxHeartbeats` | 0 | kernel heartbeat limit (thousands); 0 = none |
| `blockedHeartbeats` | 50000 | limit for an evaluation that can reach a constant without a kernel definition (such evaluations usually get stuck, and a stuck evaluation can exhaust memory first); 0 = none |
| `maxRecDepth` | 100000 | kernel recursion depth |
| `native` | true | `kdecide` only: run compiled code first, as an untrusted oracle, to fail fast on false goals |
| `wf` | true | make well-founded recursion kernel-reducible (`WellFounded.fix` ↦ `fixFuel`, proved equal) |
| `castRetry` / `castRounds` | true / 1 | when an evaluation is stuck at a cast inside a `Decidable` or `Fintype` instance, build a cast-free version, prove it equal, retry |
| `foldRetry` | true | one retry with the `@[kernel_replace_retry]` replacements and `@[kernel_fold]` patterns when one is reachable; `retryRepl := true` uses them from the start |
| `param` | true | the parametric route for definitions that occur in types, before the fallback |
| `platformCases` | true | the platform case split for terms that reach the platform word size (`USize`, so `HashMap`/`HashSet`): the kernel evaluates the term for 32 and for 64 bits, and a result that is the same for both is proved; `platformHeartbeats` (1000000) bounds each evaluation |
| `transportHeartbeats` | 20000 | heartbeat limit (thousands) for the kernel check of each copy in the fuel route's retry; 0 = none |
| `accFallback` | true | if the fuel route cannot bridge a copy, retry with the accessibility-generator route (Lean ≤ 4.36) and record it |
| `fastLitMin` | 128 | evaluate string literals of at least this many characters through a linear form (`StrFast.ofListFast`); 0 = off |
| `opt` | false | experimental: inline small definitions into copies |
| `trace` | false | print the phases and their times to standard error as they end |

For files with many `kdecide` theorems, put `set_option Elab.async false` at the top. With async
elaboration Lean keeps one thread per theorem, and their reserved address space can hit `ulimit -v`
caps, which Lean reports as "failed to create thread".

## How it works

1. **Kernel evaluation.** The kernel reduces `decide p` to `true`, as `decide +kernel` does. Compiled
   code is used only as an oracle (to fail fast, to propose witnesses or split points), and nothing it
   returns enters a proof unchecked.

2. **Copies and congruence.** For a native fact `e = true`, NativeTrust copies every definition that the
   evaluation of `e` can reach and that needs a change, and inside the copies replaces `WellFounded.fix`
   and every registered replacement by versions the kernel can evaluate. The kernel then checks the
   copied term by `rfl`, and `e = e'` is assembled by `congrArg` from per-constant equations, which the
   kernel checks at the level of definitions. Comparing an original closed term with its copy directly
   could make the kernel evaluate both, so the direct comparison is only a fallback for when congruence
   fails, and for a per-constant equation it runs under a heartbeat bound.

3. **Well-founded recursion.** Lean compiles recursion over a non-`Nat` measure to
   `WellFounded.fix … (Lean.opaqueId wf) F`, which the kernel cannot unfold. Core PR #14892 (Lean
   4.37) also removes the reduction of `WellFounded.fix` itself. In copies, NativeTrust uses `fixFuel`, a
   fuel-indexed unfolding of the functional (2^64 units, reduced lazily) that falls back to
   `WellFounded.fix`. `fix_eq_fixFuel : @WellFounded.fix = @fixFuel` is proved by induction on the fuel
   from `WellFounded.fix_eq` alone: no proof is reduced and `Acc` is not eliminated into a type. On a
   nightly with #14892 the route converted both functions we tried, and con-ron accepts its proofs.

4. **Retries.** The first attempt already applies the fuel route, registered replacements and the
   linear form of long string literals. The transformations below run only after it fails, so a fact
   that converts in the first attempt converts the same way:
   - the fuel route's retry transports proofs inside copied bodies along the copy equations
     (for example `Multiset.sort`'s proof about `mergeSort`, or `Nat.find_spec`), proves copy equations by dependent
     congruence, and leaves type formers and proofs uncopied;
   - the cast retry replaces a `Decidable` or `Fintype` instance built with a cast along `propext` or
     `Quot.sound` (for example by `simp`, `rw` or a derived `DecidableEq` with a quotient field) by a
     cast-free version, proved equal by `funext` and `Subsingleton.elim`;
   - the string retry uses the proved list-level versions of iterator-based `String` functions in
     `NativeTrust.StrLib`;
   - the parametric route rewrites definitions that also occur in types together with those types;
   - the platform case split evaluates a term that reaches `System.Platform.getNumBits` once for a 32-bit
     and once for a 64-bit word size and combines the two kernel proofs along
     `System.Platform.numBits_eq`; a result that differs between the two is not proved;
   - the accessibility-generator route (Lean ≤ 4.36) is the last fallback, recorded as `acc_fallback`.

5. **Large checks.** A cheap term is proved as it stands within `quickHeartbeats`. Otherwise the check
   is split into declarations joined by small lemmas (`&&`, `List.all`, and with `propSplit` the logical
   structure), existentials are checked at a proposed witness, and with `shards` the pieces are proved in
   separate modules compiled in parallel and combined by a module that checks each imported statement.
   With `stage`, compiled code computes the intermediate values and the kernel proves each of them in
   its own declaration, so that no declaration evaluates the whole computation. The values are hints:
   a wrong one makes a check fail, and only kernel-checked equations enter the proof.

6. **Nested facts.** A native proof inside data (`def cert := ⟨…, by native_decide⟩`) is proved first,
   and a statement that mentions such a definition is restated over its rebuilt copy, definitionally
   equal by proof irrelevance.

7. **String literals.** The kernel expands a literal to `String.ofList`, whose bytes come from a left
   fold of `Array.push`, so evaluating a literal costs time and memory quadratic in its length (a
   7,824-character literal would need about 240 GiB). Copies evaluate long literals through
   `StrFast.ofListFast`, which builds the array in one step and is proved equal.

8. **Diagnostics.** When the kernel cannot finish, the error says which case applies: false in the logic
   (the kernel reduced the term to `false`; if compiled code said `true`, the reachable
   `implemented_by` pairs are listed), blocked (a reachable constant has no kernel definition; it is
   named with the chain of definitions leading to it, and a stuck cast is located), or out of resources.
   The triage is static: it follows definition bodies as the copies would have them and evaluates
   nothing. It over-approximates: a constant on a path the evaluation never takes (a panic message, an
   error branch) is reported but does not stop the evaluation.

## What cannot be proved

These are reported precisely. Some are limits of evaluation itself rather than of the tool.

- **`partial` functions**, including `while`/`repeat` loops: in the logic a `partial def` is an opaque
  constant, so nothing about its value is provable. It must be rewritten as a total function.
- **Platform word size.** `USize` arithmetic, and through it `HashMap`/`HashSet`, depends on the opaque
  `System.Platform.getNumBits`. The platform case split proves results that are the same for 32 and 64
  bits. Results that differ, such as the iteration order of a hash map, cannot be proved, and hash maps
  keyed by strings or byte arrays stay blocked by their hashes (next item). `Std.TreeMap`/`TreeSet` are
  fine.
- **`@[extern]` primitives without a definition**: the bootstrap string operations behind `Repr`,
  `toString` and `Std.Format`, the hashes (`mixHash`, `String.hash`, `ByteArray.hash`), and transcendental `Float`
  functions. A reachable but dead use does not block anything; an evaluated use does.
- **Iterator loops** (`Std.Iter`, polymorphic ranges `a...b`, most `String.Slice` functions): they run
  on `WellFounded.extrinsicFix` with states in `Std.Shrink`, defined with an opaque constant, so no
  well-foundedness proof makes them reduce. `NativeTrust.StrLib` covers `String.Slice.foldl`/`foldr`/
  `isNat` (and so `String.toNat?` and `String.foldl`), `replace` with a `String` pattern, and `contains`
  with a `Char` or `String` pattern. Other iterator loops still block. Loops over `[a:b]`, `List` and
  `Array` work.
- **Fixpoint definitions** (`partial_fixpoint`, `Lean.Order.fix`) are defined through
  `Classical.choice`, but their fixpoint equations are theorems, so a fuel version can be proved equal and
  registered with `@[kernel_replace]`.
- **Lean's metaprogramming layer** (`Lean.Name`, `Lean.Expr`, persistent hash maps, the parser) in a
  decision procedure.
- **`bv_decide` facts** state that a certificate checker accepts a certificate. The checker parses with
  `partial` functions and hashes with opaque constants, so the library reports them as blocked. The
  add-on `addons/bvs` converts them by a separate route (below).
- **Size.** Kernel evaluation is much slower than compiled code (about 4-5 µs per kernel step) and keeps
  a cache within one declaration. Splitting, sharding and certificates bound it, but some computations
  stay out of reach. On our own published results, the facts that search large spaces or read megabytes
  of string data did not convert; for those, a kernel version written by hand remains the route.

## Add-ons

- `addons/bvs/` (Lake package): kernel-checked `bv_decide`, with the drop-in tactic `bv_kdecide`. A
  bit-blaster written for the kernel and an LRAT checker on natural-number bitmasks, both proved sound,
  while the SAT solver (CaDiCaL) is untrusted.
  It converts all 213 `bv_decide` facts of the study and its random sample, and scales to about a
  million clauses and ten million certificate hints, with sharding across modules.
- `addons/lrat/`: the bitmask LRAT checker on core's own pipeline, proved sound. It was the first route
  and is limited by the cost of core's bit-blaster in the kernel.
- `addons/primes/`: Pratt primality certificates for the field primes of common zero-knowledge and
  cryptographic libraries, for `@[kernel_fact]` (needs Mathlib).
- `addons/strrepl/`: proved list-based replacements for `String.toNat?`/`toInt?`, written for cedar-spec.
- Package-specific add-ons (BerryEsseen, BobDyLean, lean-regex, Strata, longfellow-zk, the primes of
  formal-conjectures, minidregg) are in `addons/` with notes. The minidregg add-on is licensed under
  AGPL-3.0-or-later (see License).

## Tests

`tests/` (with `.expected` outputs where the output is deterministic): `kdecide` on well-founded
recursion, strings and arrays (`Kdecide.lean`); 34 core-library goals (`Survey.lean`); false goals, a
`while` loop, a word-size-dependent fact (`USize.size = 2^64`) and a lying `implemented_by`
(`Negative.lean`); splitting (`Split.lean`); the
string replacements (`StrLib.lean`); and in `tests/kz/`: `kernelize` on module-system files and nested
facts, per-fact proving with reuse through oleans, static blockers and panic paths, the fuel route on a
nightly with core PR #14892 and its negative control (`Fuel14892.lean`, `Fuel14892Neg.lean`), the cast
retry (`CastRetry.lean`), copies in types (`TypesRepro.lean`), the platform case split
(`PlatformCases.lean`), the switch and the linter (`KernelFirst*.lean`, `Lint*.lean`, `AuditMod.lean`).
`tests/migrate_budget/` tests the per-fact budget of `migrate`.

## Files

- `NativeTrust/Basic.lean`: `fixFuel`, `fix_eq_fixFuel`, `accGen` and the assembly lemmas. It is the only
  module that generated proofs depend on, and it imports nothing beyond `Init`.
- `NativeTrust/Copy.lean`: kernel-reducible copies, their equations, congruence and transport,
  `@[kernel_replace]`, `@[kernel_replace_retry]`, `@[kernel_fold]`, `@[kernel_string_arg]`.
- `NativeTrust/Kernel.lean`: kernel checks, the routes and retries, splitting and sharding, diagnostics.
- `NativeTrust/CastFree.lean`: cast-free versions of stuck instances. `NativeTrust/Param.lean`: the
  parametric route. `NativeTrust/StrFast.lean`: linear string literals. `NativeTrust/StrLib.lean`: the
  `String` replacements. `NativeTrust/Reify.lean`: values computed by compiled code, as expressions, for
  staged evaluation.
- `NativeTrust/Tactic.lean`: `kdecide`. `NativeTrust/Kernelize.lean`: `kernelize`, `kernelize_module`,
  `trust_check`, `#kernel_blockers`, `@[kernel_fact]` and the listing commands.
- `NativeTrust/KernelFirst.lean`, `NativeTrust/KernelFirstLite.lean`, `NativeTrust/KernelBudget.lean`:
  the one-import switch, its Init-only variant, and the budget and plain-kernel verdicts they share with
  the linter (`NativeTrust/Linter.lean`).
- `NativeTrust/Driver/`: `lake exe ntrust` and `lake exe ntrust migrate`.
- `ADOPTING.md`: guide for projects. `paper/`: the paper (doi:10.5281/zenodo.23743968). `study/`: drivers, aggregators and per-fact
  results. `results_index.tsv`: for each number in the paper, the files and the command (run from the
  top directory) that reproduce it. `strlit/` and `strlit_confirm/`: the string-literal measurements.

## License

The code is licensed under the Apache License 2.0 (`LICENSE`), except the add-on in `addons/minidregg/`,
which contains code from minidregg and is licensed under the GNU Affero General Public License v3.0 or
later (`addons/minidregg/LICENSE`). The paper and the results and data in `study/`, `strlit/`,
`strlit_confirm/` and `results_index.tsv` are licensed under CC BY 4.0. Third-party material included in
the artifact is listed in `NOTICE`.
