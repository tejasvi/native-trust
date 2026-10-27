# Making computational proofs kernel-checked: a guide for verification projects

This guide is for Lean projects (verified software, certificate checkers, computer-assisted
mathematics) whose proofs use `native_decide`, `decide +native` or `bv_decide`. Each use adds an axiom
`<decl>._native.<tactic>.ax_N : decide p = true` that trusts Lean's compiler.

These axioms are refused by:
- `lake check` and Comparator, the official gates since Lean 4.35;
- Mathlib;
- the independent checkers (nanoda, con-ron).

NativeTrust re-proves such facts by kernel evaluation, without changing your sources. Where it
cannot, it says exactly why.

In a study of 52,821 native facts in 16 public packages, 9 packages converted at least 90% of their
facts automatically, while the other 7 converted at most 39%. The failures came mainly from string parsing at
check time, Lean's metaprogramming layer, `HashMap`, and time or memory limits. Among the packages
that converted:

| package | converted |
|---|---|
| cvc5/logos | 2,185 / 2,185 |
| TrainVerify | 45,707 / 45,720 |
| lido-srv3 | 70 / 70 |
| cedar-spec | every fact used in proofs |

Converted facts were re-checked by nanoda and con-ron (see the paper's section on independent checks
and `study/`).

Most converted facts never needed native evaluation. Of 51,329 converted facts that we re-ran, 51,307
convert again by plain kernel evaluation when NativeTrust's transformations are switched off; 16 need the
fuel route for well-founded recursion and 6 need splitting. For new proofs, try `decide +kernel`
first, and use `native_decide` only when kernel evaluation is too slow.

## 1. Switch with one import

Add NativeTrust to your project's dependencies (see "Installation" in the README), and import
`NativeTrust.KernelFirst` in a module imported by the modules that use `native_decide` (for instance
your project's prelude):

```lean
import NativeTrust.KernelFirst
```

Every `native_decide` and `decide +native` then works as follows:
1. It first tries `decide +kernel` within a heartbeat budget (`nativeTrust.kernelHeartbeats`,
   default 2000).
2. If the kernel proves the goal, that proof is used, and no native axiom is added.
3. Only otherwise does it run Lean's own native path, as before; an info message then gives the
   reason.

`#kernel_first_summary` lists the calls in a file and the native axioms that remain. No call needs
editing, and the switch can be turned off for a declaration or file with
`set_option nativeTrust.kernelFirst false`.

The module imports `Lean`. Like any import of `Lean`, Batteries, Aesop or Mathlib, it brings `Lean`
and `Std` into scope in every module that imports it, including module-system files, because for an
ordinary file Lean loads the whole import closure and the elaborators have to be public declarations
of `Lean` types. Their instances can change how other code elaborates. In the case we encountered,
`Std.Data.DHashMap.Raw` declares generic `Singleton`/`Insert` instances, and with them in scope a
structure-instance shorthand whose expected type is not yet known, such as
`acc ++ [{ wire, label, isolation, grok, seat }]`, elaborates as set notation and fails with "failed
to synthesize Singleton Seat Cell". In one package of a random sample, 6 modules no longer built. A
type ascription fixes such code, `acc ++ [({ wire, label, isolation, grok, seat } : Cell)]`, and so
do explicit fields, `{ wire := wire, label := label, … }`.

`NativeTrust.KernelFirstLite` is the switch for projects that cannot take `Lean` imports. It
imports nothing but `Init`: it consists of two macros, so nothing else changes in the modules that
import it. Each `native_decide` and `decide +native` written without further configuration tries
`decide +kernel` within 2000 thousand heartbeats and otherwise runs the original call, which leaves
the same native axiom as without the switch. Compared with `NativeTrust.KernelFirst` it lacks:
- the options: it cannot be switched off for a declaration, and its budget is fixed
  (`nativeTrust.kernelFirst` and `nativeTrust.kernelHeartbeats` do not exist without
  `NativeTrust.KernelFirst`);
- the report: no info message with the reason when a call falls back;
- `#kernel_first_summary`;
- the static triage, so a call that the kernel cannot check can use its whole budget before it falls
  back;
- calls written with configuration, such as `native_decide +revert`, which it leaves to Lean.

When both modules are loaded, the macros leave every call to the elaborators.

On unmodified sources, adding only this import took the native axioms of lido-srv3 (whole package,
723 modules) from 70 to 0 with either module, and those of cvc5/logos's 10 largest modules from 1,043
to 0 with `NativeTrust.KernelFirst`. The effect on build time depends on the facts involved. With
`NativeTrust.KernelFirst`, cvc5's 10 modules took 184.7 s instead of 187.6 s, and lido-srv3 345 s
instead of 343 s. With `NativeTrust.KernelFirstLite`, lido-srv3 took 421 s instead of 360 s (one run
each); without the static triage, a call that the kernel cannot check can use its whole budget
before it falls back. The 11 small modules of codegraff took 13-15 s with Lite and 17 s with
`NativeTrust.KernelFirst` (on a copy in which the 6 shorthands were fixed) instead of 2-2.6 s; most of
that time is kernel evaluation.

## 2. Keep new code free of unnecessary native_decide

With `set_option linter.nativeTrust true`, Lean warns at each `native_decide` whose goal
`decide +kernel` proves:
"native_decide is unnecessary here", with a "Try this: decide +kernel" fix. It also warns at each
fact that can never be kernel-checked, naming the blocking constant.
- `linter.nativeTrust.strict` turns the "unnecessary" warning into an error, so that CI can enforce it.
- `#native_decide_audit` (or `#native_decide_audit M`) prints a verdict for every native fact in a
  module: replaceable, needs NativeTrust, blocked, too expensive, or stuck.

## 3. Convert what remains, without changing sources

Add NativeTrust (Lean 4.27 through 4.35 and current nightlies) to your project's dependencies,
then run from the project root:

```
lake exe ntrust --jobs 8
```

The command:
1. finds the modules that use native evaluation and builds them;
2. proves each native fact in its own process, under a time and memory limit;
3. writes `.ntrust/report.tsv`, one line per fact with its verdict and, for a failure, the
   blocking constants;
4. writes `.ntrust/Kernel/`, a kernel supplement: for every theorem `T` that uses native facts, in each
   module that uses a native tactic, a theorem `T.kernel` with the same statement (or one over rebuilt
   definitions) and only the standard axioms;
5. writes `.ntrust/comparator.json`, which pairs each original theorem with its kernel version for
   Comparator.

Facts used by other facts (`def cert := ⟨…, by native_decide⟩`,
`instance : Fact (Nat.Prime p) := by native_decide`) are proved once and reused. Proofs of
well-founded functions use a fuel construction that needs no reduction of proofs; on a nightly with
core PR #14892 it converted both functions we tried, and con-ron accepts such proofs.

Interactive variants:
- `kernelize T` adds `T.kernel` for one theorem.
- `trust_check T` gives CLEAN, KERNELIZED or REJECTED with the reason.
- `kdecide` replaces `native_decide` directly in new proofs.

## 4. Design new checkers for the kernel

Checker designs that convert automatically:

- Data as `List`, `Array`, `Nat`, `Int`, `Fin`, `BitVec`, and `Std.TreeMap`/`TreeSet`.
- Structural recursion, or `termination_by` with a `Nat` measure. Other measures also work through
  the fuel construction.
- Loops over `List`, `Array`, or `[a:b]` ranges.
- Large checks written as `l.all f` or `a && b`: NativeTrust splits them into separate kernel
  declarations, which bounds memory.

Designs that make a fact native-only for good:

| construct | why | alternative |
|---|---|---|
| parsing `String` data at check time (`splitOn`, `replace`, `toNat?`) | iterator loops whose state types are defined with an opaque constant (NativeTrust's `StrLib` replaces `toNat?`, `foldl`, `replace` and `contains` in a retry, other functions still block); also, kernel evaluation of a non-repetitive string literal is quadratic in its length (4.4 GiB at 1,000 characters, `strlit/`), which NativeTrust's copies avoid for long literals | store certificates as `List Nat` / `Array Nat` literals |
| `HashMap`, `HashSet`, `USize` | platform word size and C hash primitives | `Std.TreeMap`, sorted lists |
| `partial def`, `while` loops, `partial_fixpoint` | no equations in the logic | structural recursion or fuel |
| transcendental `Float` functions (`Float.log`), custom C code | no definition in the logic | rational or integer arithmetic |
| `bv_decide` | its LRAT checker parses with `partial` functions and hashes with opaque constants | the add-on `addons/bvs` (a bit-blaster written for the kernel and a bitmask LRAT checker, both proved sound; the SAT solver is untrusted) converts all 213 `bv_decide` facts of the study and its random sample, up to about a million clauses |
| evaluating through metaprogramming (`Lean.Syntax`, environment extensions) | `partial`/unsafe implementations | keep checkers in plain data |
| decidability instances obtained by a cast (`simp <;> infer_instance`, `h ▸ inferInstance`, derived instances on quotients) | the kernel cannot reduce `Eq.rec` along an equality proved with `propext` or `Quot.sound`; compiled code erases the cast | build the instance with `decidable_of_iff` (its proof is never evaluated) or by direct recursion |

`NativeTrust.StrLib` (Lean 4.30 and later) gives proved list-level versions of `String.toNat?`,
`String.foldl`, `String.replace` with a `String` pattern and `String.contains` with a `Char` or
`String` pattern; NativeTrust uses them in a retry after the first attempt fails. With them, all 16
string facts of cedar-spec convert without a package add-on. Other functions that take a pattern,
however, still block, because core has no lemmas that characterize them by lists. The earlier add-on
`addons/strrepl/StrRepl.lean` (registered with `@[kernel_replace]`) covers `String.toNat?`/`toInt?`
alone.

Primality side conditions (`Fact (Nat.Prime p)`) should be proved with certificates (`norm_num`
for small primes, Pratt certificates for large ones). Register them with `@[kernel_fact]`, and every
fact that mentions the field then converts. In one zk-circuit library this raised conversion from
17/120 to 116/120.

## 5. Continuous integration

A minimal CI job:

```yaml
- run: lake build            # with the strict linter options below in the CI configuration
- run: lake exe ntrust --jobs 4 --fact-timeout 900
- run: lake env lean .ntrust/Kernel/All.lean   # the supplement must build
```

To make every unnecessary `native_decide` a build error, pass the options
`-Dweak.linter.nativeTrust=true -Dweak.linter.nativeTrust.strict=true` to Lean, e.g.
`moreLeanArgs = ["-Dweak.linter.nativeTrust=true", "-Dweak.linter.nativeTrust.strict=true"]` in the
library's section of `lakefile.toml`. These options were tested with `lean` directly, but not yet
through Lake. Fail the job on any fact whose verdict changed from PROVED. Publish the report as an artifact.
Archive the kernel supplement next to the native release, so that the result can be re-verified
without running compiled code.

## 6. What remains trusted

A converted fact relies on Lean's kernel, including the kernel's built-in arithmetic on natural
numbers, and on the three standard axioms, instead of code generated by Lean's compiler. The
NativeTrust meta-code is outside the trusted base: every declaration it generates is checked by the kernel, and the outputs can be
re-checked by nanoda and con-ron with `lean4export`.
