# bvs: kernel-checked re-proofs of `bv_decide` facts

`bv_decide` proves a goal about bit vectors by reducing it to the unsatisfiability of a formula
`E : Std.Tactic.BVDecide.BVLogicalExpr` and closing it with
`Std.Tactic.BVDecide.Reflect.unsat_of_verifyBVExpr_eq_true E C h`. Here `C` is an LRAT certificate
from a SAT solver, and `h : verifyBVExpr E C = true` is established by compiled (native) evaluation.
In the Lean versions this package was tested with, `h` is an auxiliary axiom named
`…._native.bv_decide.ax_…`.

This package proves `Std.Tactic.BVDecide.BVLogicalExpr.Unsat E` in Lean's kernel, without native
evaluation. It then adds a copy of the original theorem in which `unsat_of_verifyBVExpr_eq_true E C h`
is replaced by that proof. The copy has the same statement as the original but depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`. The original theorem is not changed, so other
declarations that refer to it still depend on the native axiom.

In new and existing proofs, the tactic `bv_kdecide` can be written instead of `bv_decide`. It proves the
same goals by the same route and adds no native axiom, so nothing needs converting afterwards (see
"The tactic `bv_kdecide`" below).

## How it works

The kernel checks three things. Each check is a Boolean function evaluated on data, where the data
are definitions produced by compiled code.

1. **Bit-blasting.** `BVS.Blast` is a bit-blaster written for kernel evaluation. It uses structural
   recursion over lists and natural numbers, and no arrays or hash maps. It turns `E` into a list of
   AND gates and input bits, and the Tseitin clauses of the gates form the CNF. The soundness theorem
   `BVS.unsat_of_cnf` states that an unsatisfiable CNF implies `E.Unsat`.
2. **The clauses.** The original clauses (stored as gate descriptors) and the learned clauses of the
   certificate are kept in a perfect binary tree. The kernel checks that the tree holds the CNF.
3. **The certificate.** The certificate is CaDiCaL's LRAT proof, trimmed to the steps that the empty
   clause needs. Each hint is annotated with the literal it makes unit. The kernel checks it by reverse
   unit propagation on bitmasks, in chunks of at most 2000 steps or 20000 hints, one declaration per
   chunk.

Because the kernel keeps all intermediate terms of a declaration until the declaration is checked,
splitting the work across declarations bounds the memory that each declaration needs. The chunk
declarations can be put into separate modules (shards) and compiled in parallel. For large problems,
the checks of steps 1 and 2 can also be split (the split base check): the bit-blaster's run becomes
one declaration, and the well-formedness of the gates and the placement of their clauses in the tree
become one declaration per segment of gates.

## Trusted base

Lean's kernel checks the theorems by evaluating Boolean functions that compute with natural numbers.
For `Nat` addition, subtraction, multiplication, division, modulo, comparison, bitwise operations and
shifts, the kernel uses its built-in arbitrary-precision (GMP) implementations, which are part of the
trusted base. The
proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`; they do not use
`Lean.ofReduceBool` or `Lean.trustCompiler`.

The following parts are untrusted:

- the SAT solver;
- the compiled bit-blasting that produces the data;
- the processing of the certificate (trimming, renumbering, hint annotation);
- the commands that build the proof terms.

An error in these parts can make a conversion fail, but it cannot produce a theorem that the kernel has
not checked.

## Requirements

- Lean 4. `lean-toolchain` selects v4.35.0. The package was also built on v4.31.0, v4.32.2, v4.33.1,
  v4.34.1, v4.35.0-rc4 and v4.36.0-rc1; on each of them the audit file showed only the standard axioms
  and all examples re-proved. On v4.30.0 a proof script in `BVS/Sound/Expr.lean` fails. Versions up to
  v4.29 lack `Std.Tactic.BVDecide.BVUnOp.cpop`. All files of the package are modules of Lean's module
  system, so `import BVS` works both in files that start with `module` and in other files.
- CaDiCaL. By default the commands run the `cadical` executable that Lean toolchains ship for
  `bv_decide`, in the same directory as the running `lean` executable. The option `bvs4.cadical` sets
  another path. The solver is called as
  `timeout <bvs4.timeout> cadical <file>.cnf <file>.lrat --lrat --binary=true --quiet --shrink=0 --unsat`.
  This needs the `timeout` command (GNU coreutils) on `PATH`. The two files are written to
  `bvs4.workdir` (default: the current directory) and removed after use unless `bvs4.keepFiles` is set.
- For sharding: `bash`, `xargs`, and `lake` on `PATH`.
- The package was tested on Linux only.

## Using it

Add the package to your Lake project, for example with

```toml
[[require]]
name = "bvs"
path = "path/to/bvs"
```

and `import BVS`.

### One theorem

```lean
import BVS

theorem mul_three (x : BitVec 16) : x * 3 = x + x + x := by bv_decide

bvs4_kernelize mul_three   -- adds `mul_three.bvs4 : ∀ x : BitVec 16, x * 3 = x + x + x`
```

`bvs4_kernelize t` replaces every `unsat_of_verifyBVExpr_eq_true` in the proof of `t` and adds
`t.bvs4`. It fails if the new theorem depends on axioms other than the standard three.

### The facts of a module

- `bvs4_module M` converts every `bv_decide` axiom of the imported module `M`. The i-th axiom
  (counting from 1) gives `bvs4fact_<i>.unsat`. Each theorem of `M` that uses one of these axioms is
  re-proved as `bvs4thm_<j>.bvs`.
- `bvs5_list M` prints the `bv_decide` axioms of `M` with their indices (counting from 0).
- `bvs5_fact M i₁ i₂ …` converts the selected axioms (theorems `bvs5fact_<i>.unsat`). It then rebuilds
  every declaration of `M` whose value depends on them, directly or through other declarations of `M`,
  as `bvs5_<k>` with the original type, in dependency order. Theorems and definitions are both rebuilt.

`bvs4_kernelize` and `bvs4_module` report their results as messages. The `bvs5`, `bvs5_group` and
`bvs6` commands print one line per fact (`BVS_UNSAT`) and one per rebuilt declaration (`BVS_USER`, with
the original name, the new name, whether the type is identical, and whether only standard axioms are used)
to standard error.

### Facts from several modules

When a theorem uses facts from several modules or packages, the facts must be converted together.
Converting each module on its own rebuilds the module's declarations, but a rebuilt declaration that refers
to a theorem of another module refers to the original theorem, which still depends on its native axiom.
`bvs5_group "M₁:i,j,…" "M₂:k,…" …` converts the selected facts of all listed modules in one process
(theorems `bvsg_<M>_<i>.unsat`, with the dots of `M` replaced by `_`). It then rebuilds every declaration
of these modules that depends on them, in dependency order and with references to the rebuilt versions
across modules (`bvsg_<k>`, original types). The modules must be imported; for facts in several packages,
the importing project depends on all of them. `Examples/Group.lean` converts two facts from two modules in
this way.

### Sharding

A prep file names the facts; compiling it runs the solver, defines the data, proves the base check
and writes `k` shard files and a final file into a directory. The shard files, which contain the chunk
theorems, can be compiled in parallel; the final file then imports the shards, assembles the theorems
and rebuilds the declarations that use them.

| prep command | facts | final command |
|---|---|---|
| `bvs4_prep_module M "dir" k` | all `bv_decide` axioms of `M` | `bvs4_assemble_module M` |
| `bvs5_prep M "dir" k i₁ i₂ …` | the selected axioms | `bvs5_assemble M i₁ i₂ …` |
| `bvs6_prep M "dir" k S i` | one axiom, with the split base check (segments of `S` gates) | `bvs6_assemble M i` |

The prep command writes the final command into the final file. With `bvs6_prep`, the shard files
also prove the bit-blaster's run (`bvs6_blast`) and one theorem per segment (`bvs6_seg`). The results
are named as for the corresponding one-process commands: `bvs4fact_<i>.unsat` and `bvs4thm_<j>.bvs`
for `bvs4_prep_module`, `bvs5fact_<i>.unsat` and `bvs5_<k>` for `bvs5_prep`, and
`bvs6fact_<i>.unsat` and `bvs6_<k>` for `bvs6_prep`.

The workflow:

1. Put the facts in a module of your package and build it, for example `lake build My.Facts`.
2. Write a prep file, for example `MyPrep.lean`:

   ```lean
   import BVS
   import My.Facts

   bvs5_prep My.Facts "." 4 0 2
   ```

   The directory argument is relative to the working directory of the `lean` process. With the
   script below, use `"."`.
3. From the root of your package, run `path/to/bvs/scripts/shard.sh MyPrep.lean WORK_DIR [JOBS]`.
   The script compiles the prep file in `WORK_DIR`, then the shard files (`JOBS` at a time, default 4),
   then the final file.
4. The converted theorems are in the module `MyPrep_Final` (`WORK_DIR/MyPrep_Final.olean`). Add
   `WORK_DIR` to `LEAN_PATH` to import it.

### Options

Set these with `set_option` before a command.

| option | default | meaning |
|---|---|---|
| `bvs4.chunk` | 2000 | maximal LRAT steps per chunk declaration |
| `bvs4.chunkHints` | 20000 | maximal hints per chunk declaration (a single step may exceed it) |
| `bvs4.timeout` | 600 | SAT solver time limit in seconds |
| `bvs4.workdir` | current directory | directory for the DIMACS and LRAT files |
| `bvs4.keepFiles` | false | keep the DIMACS and LRAT files |
| `bvs4.cadical` | `cadical` next to `lean` | the solver executable |
| `bvs4.log` | none | file to which progress lines (sizes, time per declaration) are appended |

## The tactic `bv_kdecide`

`bv_kdecide` proves the goals that `bv_decide` proves, with a proof that Lean's kernel checks. Write it
where `bv_decide` would be:

```lean
import BVS

theorem mul_three (x : BitVec 16) : x * 3 = x + x + x := by bv_kdecide

#print axioms mul_three   -- [propext, Classical.choice, Quot.sound]
```

The theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. No `_native.bv_decide.ax_…`
axiom is added to the environment, so nothing has to be converted afterwards, and declarations that use the
theorem need no rebuilding.

The tactic takes the configuration of `bv_decide` and passes it on, for example
`bv_kdecide (config := { timeout := 60 })` or `bv_kdecide +acNf`.

### Example: a project's own tactic

Projects often call `bv_decide` through a macro of their own. veir proves most of its 188 `bv_decide` facts
through `veir_bv_decide`, defined in `Veir/Meta/Tactic/BVDecide.lean`. With this package added to the
project's dependencies, two changes to that file are enough:

```diff
 public import Veir.Meta.Tactic.BVNormalizeSimp
+public import BVS
 ...
 @[expose] macro "veir_bv_decide" : tactic =>
-  `(tactic| ((veir_bv_normalize <;> bv_decide (config := { timeout := 300 }))))
+  `(tactic| ((veir_bv_normalize <;> bv_kdecide (config := { timeout := 300 }))))
```

With this file changed and nothing else, veir's module `Veir.Passes.RISCVCombines.Proofs` compiled with 68
kernel-checked uses of the macro; its compiled module declares no `_native` name, and all 68 of its theorems
depend only on the standard axioms.

### How the tactic works

1. `bv_decide` runs on a copy of the goal, in a scope whose changes to the environment are discarded.
   Its proof term ends in `Reflect.unsat_of_verifyBVExpr_eq_true E C ax`, where `E` is the reflected
   problem, `C` the LRAT certificate and `ax` the native axiom.
2. The environment is restored, so `ax`, `C` and the other auxiliary declarations of `bv_decide` are not
   added. (Declarations that the rest of the proof needs, such as `T.enumToBitVec` for an enumeration type
   `T`, are created again by `bv_decide`'s preprocessing alone.) The tactic defines `E` again and proves
   `E.Unsat` with the pipeline of `bvs4_kernelize`: the base check in one declaration and the LRAT chunks in
   one declaration each. When the CNF has more than `bvs4.splitAbove` clauses, the base check is split as in
   `bvs6_prep`: one declaration for the bit-blaster's run and one per segment of `bvs4.segment` nodes. The
   declarations are named `<decl>._bvk_<i>.…`, and the result is the theorem `<decl>._bvk_<i>.unsat`.
3. In the proof term of step 1, `unsat_of_verifyBVExpr_eq_true E C ax` is replaced by that theorem, and the
   goal is closed with the result. The tactic fails if the term still depends on a native axiom.

If `bv_decide` fails, `bv_kdecide` fails with the same error. If the preprocessing of `bv_decide` closes
the goal without a SAT call, its proof is used as it is. The tactic does not use `C`: like
`bvs4_kernelize`, it solves the CNF of the kernel bit-blaster.

### Tactic options

| option | default | meaning |
|---|---|---|
| `bvs4.splitAbove` | 200000 | use the split base check when the CNF has more clauses than this |
| `bvs4.segment` | 30000 | nodes per segment of the split base check |
| `bvs4.stats` | false | report sizes, times and (on Linux) the peak memory of each call in an information message, and in the `bvs4.log` file if one is set |

The options `bvs4.timeout`, `bvs4.chunk`, `bvs4.chunkHints`, `bvs4.cadical` and `bvs4.log` work as for the
commands. The solver files go to `bvs4.workdir` if it is set, otherwise to the system's temporary
directory (`TMPDIR`). The kernel checks of the tactic run without a heartbeat limit and with `maxRecDepth`
at least 1000000, as in the shard files of `bvs6_prep`; their heartbeats do not count against
`maxHeartbeats` for the rest of the proof. With `Elab.async` on (the default), the times reported by
`bvs4.stats` can include time spent waiting for other declarations; set `Elab.async false` for exact times.

### Cost

`bv_kdecide` costs what `bv_decide` costs plus the kernel route, which is the same work as
`bvs4_kernelize` (see Measured results). On the examples of this package, a file with `bv_kdecide` took as
long as the same file with `bv_decide` followed by `bvs4_kernelize`, within 5%. The `bv_decide` run inside
the tactic is small next to the kernel route: on the 195 facts below, its median was 59 ms.

Single facts, each in its own `lean` process (times include `import BVS`, which alone takes 0.5 s and
1.5 GiB). For comparison, the 8192-bit fact took 2,322 s and 50.2 GB with `bvs4_kernelize` and the single
base check (Scale, below); the split base check of the tactic keeps it at 12.7 GiB.

| goal | CNF clauses | LRAT steps | hints | `bv_decide` | `bv_kdecide` | peak |
|---|---|---|---|---|---|---|
| `x * 3 = x + x + x`, 16 bits | 959 | 267 | 5,687 | 0.6 s | 1.8 s | 1.7 GiB |
| `(~~~x).cpop + x.cpop = 16#16`, 16 bits | 3,344 | 1,947 | 40,472 | 0.6 s | 8.6 s | 2.2 GiB |
| `x * 3 = x + x + x`, 128 bits | 8,351 | 5,543 | 89,806 | 0.6 s | 27.1 s | 2.5 GiB |
| `x * 3 = x + x + x`, 256 bits | 16,799 | 21,697 | 183,793 | 0.6 s | 67.5 s | 2.8 GiB |
| `x * (y * z) = (x * y) * z`, 5 bits | 1,679 | 6,837 | 303,653 | 0.8 s | 42.0 s | 2.2 GiB |
| `(x &&& y) + (x ||| y) = x + y`, 1024 bits | 73,697 | 114,328 | 232,083 | 1.1 s | 204 s | 6.9 GiB |
| `x * 3 = x + x + x`, 512 bits | 33,695 | 44,205 | 1,409,291 | 0.6 s | 395 s | 4.5 GiB |
| `x * 3 = x + x + x`, 1024 bits | 67,487 | 105,748 | 1,671,167 | 0.6 s | 557 s | 7.1 GiB |
| `(x &&& y) + (x ||| y) = x + y`, 4096 bits (split base check, 4 segments) | 294,881 | 461,298 | 935,026 | 2.5 s | 927 s | 7.8 GiB |
| `(x &&& y) + (x ||| y) = x + y`, 8192 bits (split base check, 8 segments) | 589,793 | 918,490 | 1,863,909 | 5.2 s | 1,995 s | 12.7 GiB |

Facts of other packages: every `bv_decide` fact of the modules involved, copied with `bv_decide` (in veir:
its macro) replaced by `bv_kdecide`, one `lean` process per module, `Elab.async` off. A fact is a call that
needs the SAT solver; memory is the peak of the process during the call.

| package (Lean version): facts | median | 90th percentile | maximum | sum | memory: median, maximum |
|---|---|---|---|---|---|
| veir (v4.35.0-rc4): 187 | 2.0 s | 53.1 s | 2,889 s | 14,456 s | 1.8 GiB, 16.8 GiB |
| clean (v4.33.1): 4 | 1.8 s | 2.0 s | 268 s | 272 s | 1.8 GiB, 6.7 GiB |
| Natuvea (v4.31.0): 3 | 1.9 s | 1.9 s | 46.1 s | 48 s | 7.0 GiB, 8.7 GiB |
| asi-stack-book (v4.31.0): 1 | 1.3 s | 1.3 s | 1.3 s | 1 s | 1.6 GiB, 1.6 GiB |

Most facts are cheap, but a few are very expensive. With a limit per fact, a rewrite of `bv_decide` into
`bv_kdecide` would keep these facts and add this much build time (the time of `bv_kdecide` minus that of
`bv_decide`, summed):

| limit per fact | facts kept (of 195) | added build time |
|---|---|---|
| 1 s | 64 | 14 s |
| 10 s | 148 | 263 s |
| 60 s | 176 | 1,018 s |
| 300 s | 186 | 2,287 s |
| none | 195 | 14,724 s |

The largest fact, veir's `sdivPow2Exact_neg_refinement` (854,213 clauses, 8.7 million hints, split base
check with 10 segments), took 48 minutes and 16.8 GiB. veir's module `Veir.Passes.InstructionSelection.Proofs`
without its 7 largest facts (101 facts) took 47 s with `bv_decide` and 2,554 s with `bv_kdecide`, at a peak
of 9.1 GiB.

### Estimating the cost

`bvs5_estimate M` lists the `bv_decide` axioms of an imported module `M` (with the indices of `bvs5_list`),
the size of the kernel bit-blaster's CNF for each, and an estimate of the time `bv_kdecide` takes for it.
It runs the bit-blaster only (no SAT solver, no kernel check), in about a second per module. The estimate
is `0.064 · clauses ^ 1.355` ms, fitted on an earlier run of these facts. On the 131 facts that took
more than a second, its median relative error is 31 % (90th percentile 95 %); it overestimates the largest facts,
which use the split base check, by a factor of 2 to 4, and the sum by a factor of 1.85. For a limit of 60 s
per fact it makes the same keep-or-skip decision as the measured times for 192 of the 195 facts. The time
of `bv_kdecide` follows the size of the kernel bit-blaster's CNF closely (rank correlation 0.98), and the
size or time of `bv_decide` less (0.79 for the size of its certificate, 0.76 for its time), because
`bv_decide` simplifies the problem and merges equal subcircuits before it bit-blasts.

### Limits

- All of the work happens in one process and one module. The split base check keeps the memory of large
  facts bounded (the largest fact above: 16.8 GiB), but the time adds up; the sharded commands
  (`bvs5_prep`, `bvs6_prep`) check the chunks of a fact in parallel.
- The SAT problem is solved twice: by `bv_decide`, and for the CNF of the kernel bit-blaster.
- The data of the kernel checks stay in the compiled module (the certificates of `bv_decide` do not):
  veir's `Veir.Passes.RISCVCombines.Proofs` (39 facts) grew from 1 MiB to 6 MiB, Natuvea's
  `Model.CompositeHeader` (2 facts) from 1 MiB to 14 MiB, clean's `ByteDecomposition.Theorems` (1 fact) from
  39 MiB to 62 MiB.
- Because the kernel bit-blaster does not merge equal subcircuits, the certificate for goals with
  multipliers can be far larger than the one that `bv_decide` checks: `x * y = y * x` at 8 bits needs 37,524 LRAT steps and
  1.38 million hints, and its kernel checks take about 225 s.
- Only the configuration syntax of `bv_decide` is accepted, not its `types [...]` clause. Tactics that call
  `bv_decide`'s implementation directly rather than through its syntax (veir's `pbv_decide`, used for one
  fact) are not affected by replacing `bv_decide` with `bv_kdecide`.
- Several large `bv_kdecide` goals in one file can be checked at the same time when `Elab.async` is on and
  Lean uses several threads; their memory adds up. `LEAN_NUM_THREADS=1` or `Elab.async false` avoids this.
- Lean v4.31.0 and later, as for the rest of the package (see Requirements). Projects on v4.29 or v4.30
  (for example Radix, v4.29.0-rc4) cannot use it.

## Soundness theorems

`Audit.lean` prints the axioms of these 15 theorems. It also checks that the conclusions of
`BVS.bvs_unsat4`, `BVS.bvs_unsat5` and `BVS.unsat_of_cnf` are core's
`Std.Tactic.BVDecide.BVLogicalExpr.Unsat`.

- `BVS.unsat_of_cnf`: if `bv` uses supported constructors, the bit-blaster's gates for `bv` pass the
  well-formedness check `wfEs`, and no assignment satisfies their CNF `cnfOf`, then `bv.Unsat`.
- `BVS.blastBool_spec`: under every valuation that respects the gates of the final state, the output
  literal of `blastBool` has the value of the formula under the assignment.
- `BVS.blastUn_spec`: for every unary operation (`not`, rotations, arithmetic shift by a constant,
  `reverse`, `clz`, `cpop`), the output literals evaluate to the bits of `op.eval x` when the input
  literals evaluate to the bits of `x`.
- `BVS.blastClz_spec`: the count-leading-zeros circuit computes `BitVec.clz`.
- `BVS.blastCpop_spec`: the population-count circuit computes `BitVec.cpop`.
- `BVS.bitsOf_reverse`: the bits of `x.reverse` are the bits of `x` in reverse order.
- `BVS.chkUR_sound`: if a chunk of LRAT steps passes `chkUR` from id `s`, every assignment that
  satisfies the clauses below id `s` also satisfies the clauses of the chunk (`ChainL`).
- `BVS.bvs_unsat4`: the base check `check4` (bit-blasting, well-formedness, the tree holds the CNF),
  a chain of chunks from the first learned clause to the last, and the empty clause at the last id
  imply `bv.Unsat`.
- `BVS.blastCk_sound`: `blastCk bv es n out = true` means that `bv` uses supported constructors and
  that the bit-blaster's run on `bv` gives the gate list `es`, the next node `n` and the output literal
  `out`.
- `BVS.agreeFrom_sound`: if the in-order pass over a subtree from key `lo` succeeds, the `i`-th given
  leaf that falls into the subtree is stored at key `lo + i`, and the pass returns the remaining leaves.
- `BVS.agreeSeg_sound`: if `agreeSeg T D lo xs = true`, the `i`-th leaf of `xs` is stored in `T` at
  key `lo + i`, for every `i`.
- `BVS.wfEs_append`: a concatenation of gate segments is well formed if each segment is well formed
  with respect to the bound that the newer segments leave.
- `BVS.gateLeaves_append`: the clauses of a concatenation of segments are the clauses of the older
  segment followed by those of the newer segment.
- `BVS.acc_step`: a segment that passes `segOK` (well-formedness, its clauses in the tree, their
  number) extends the checked part of the gate list (`EntsOK`).
- `BVS.bvs_unsat5`: `blastCk`, the checked gate list, the first two clauses in the tree, a chain of
  chunks and the empty clause imply `bv.Unsat`.

## Examples and checks

- `lake build` builds the library, and `lake env lean Audit.lean` runs the axiom audit.
- `lake build Examples` re-proves the facts of `Examples/Small.lean` (four small facts) and
  `Examples/UnaryOps.lean` (`reverse`, `clz`, `cpop`). It also builds the fact modules of the sharded
  examples.
- `Examples/Group.lean` (also built by `lake build Examples`) converts the facts of `Examples/GroupA.lean` and
  `Examples/GroupB.lean` with `bvs5_group` and rebuilds a theorem that uses both.
- `scripts/shard.sh prep/ShardPrep.lean WORK_DIR 2` converts two facts with `bvs5_prep` in two shards.
- `scripts/shard.sh prep/SplitPrep.lean WORK_DIR 2` converts one fact with the split base check
  (`bvs6_prep`, segments of 2000 gates).

## Measured results

The times below are wall-clock times of single-threaded Lean processes (`LEAN_NUM_THREADS=1`) on a
Linux server shared with other jobs. They include importing the libraries and running core's
`bv_decide`, unless stated otherwise. Memory figures are peak resident set sizes. Repeated runs varied
by up to about 20%.

### Facts from Lean packages

These are facts from other Lean packages that `bv_decide` proves with a native axiom. They were
converted with `bvs4_module` in one process each. The `clean` facts used Lean v4.33.1, and the
asi-stack-book fact used v4.31.0.

| module | CNF clauses | LRAT steps | hints | kernel: base + chunks | file | peak |
|---|---|---|---|---|---|---|
| `Clean.Utils.Bitwise` | 2 | 1 | 2 | 0.06 s + 0.00 s | 1.3 s | 2.7 GB |
| `Clean.Gadgets.And.And8` | 1,187 | 449 | 7,503 | 0.46 s + 1.5 s | 3.4 s | 3.0 GB |
| `Clean.Gadgets.Or.Or8` | 1,205 | 385 | 5,319 | 0.42 s + 1.2 s | 3.0 s | 3.0 GB |
| `AsiStackProofs.StackBoundaries` | 1,424 | 362 | 840 | 0.67 s + 0.32 s | 1.7 s | 1.7 GB |
| `Clean.Gadgets.ByteDecomposition.Theorems` | 65,720 | 31,056 | 959,442 | 28.5 s + 246 s | 303 s | 8.2 GB |

With `bvs4_prep_module` and four shards, the ByteDecomposition fact took 115 s of wall time: 51 s for
the prep file, 49 s to 62 s per shard (in parallel, at most 4.2 GB each) and 2.3 s for the final file.

### All `bv_decide` facts of six packages

A sweep covered all 213 `bv_decide` facts of six Lean packages: veir 188, Radix 17, clean 4,
tacenta-model 2, tacenta-proofs 1 and asi-stack-book 1. Each fact ran in its own process with a 900 s
time limit, a 48 GB address-space limit and one thread.

- 197 facts converted in that setting.
- 3 facts needed more than 900 s. They converted with `bvs5_prep` and four shards in 24 minutes for all
  three: 630 s for the prep file, 774 s for the shards and 21 s for the final file.
- 4 facts with 588,000 to 854,000 clauses ran out of memory in the single base check. They converted
  with `bvs6_prep`. The bit-blaster declarations took 64 s to 91 s, and each full segment of
  30,000 gates took 25 s to 37 s. No process exceeded 15.2 GB. With four shards, one of these facts
  took about 12 minutes of wall time.
- 9 facts use `reverse`, `clz` or `cpop`, which the bit-blaster now supports.

All 213 converted theorems depend only on the standard axioms (`#print axioms` in fresh processes),
and every rebuilt declaration has the type of its original. In two places, declarations use facts that
the sweep converted in different runs: `llvmLoad`, `memcpy` and `memmove` in veir's
`Veir.Interpreter.Memory` use both facts of that module, and `decode_encode` and `decode_encode_composite`
in tacenta-proofs use the two facts of tacenta-model. Converted together with `bvs5_group`, all 13 rebuilt
declarations of these two groups depend only on the standard axioms in a fresh process, and nanoda accepted
exports of both groups (7,058 and 4,519 declarations). In one module,
`RISCVCombines.Combine` of veir, all 30 facts and all 59 declarations built from them were rebuilt
with standard axioms only, including the module's final definition. nanoda, an independent type
checker, accepted exports of 26 facts sampled in the sweep and of five later conversions, which cover
sharding, the split base check and the three new operations. An earlier route, which evaluates
core's bit-blaster in the kernel, converted 127 of the 213 facts.

### Comparison with lean-dedep

The goal was `theorem mul_three (x : BitVec w) : x * 3 = x + x + x := by bv_decide`, followed by
`bvs4_kernelize mul_three`. The runs used Lean v4.33.1, one thread and a 40 GiB address-space limit.
The times are for the whole file. The numbers for lean-dedep are quoted from its README
(w = 2 to 6: 1, 3, 7, 17, 48 s; w = 16 did not finish in 10 minutes). They were measured on a
different machine, and lean-dedep was not run here.

| w | CNF clauses | LRAT steps | hints | kernel checks | file | peak |
|---|---|---|---|---|---|---|
| 4 | 167 | 56 | 351 | 0.14 s | 0.82 s | 1.6 GB |
| 6 | 299 | 76 | 1,022 | 0.41 s | 1.08 s | 1.6 GB |
| 8 | 431 | 150 | 2,051 | 0.73 s | 1.65 s | 1.7 GB |
| 16 | 959 | 267 | 5,687 | 1.65 s | 2.34 s | 1.8 GB |
| 32 | 2,015 | 600 | 14,717 | 3.64 s | 4.40 s | 2.1 GB |
| 64 | 4,127 | 1,640 | 42,371 | 11.0 s | 11.9 s | 2.3 GB |
| 128 | 8,351 | 5,543 | 89,806 | 28.3 s | 30.0 s | 2.6 GB |
| 256 | 16,799 | 21,697 | 183,793 | 72.7 s | 77.5 s | 3.1 GB |
| 512 | 33,695 | 44,205 | 1,409,291 | 455 s | 468 s | 4.9 GB |
| 1024 | 67,487 | 105,748 | 1,671,167 | 617 s | 651 s | 7.8 GB |

These runs used the version of the sources before `reverse`, `clz` and `cpop` were added, but a rerun
of w = 4 to 256 with the current sources gave the same CNF and certificate sizes. The bit-blaster does not
merge equal subcircuits, so the two sides of the goal give different circuits, and even small widths
need a SAT proof.

### Scale

- One process with the single base check: `(x &&& y) + (x ||| y) = x + y` at 4096 bits
  (294,881 clauses, 935,026 hints) took 146 s for the base check and 950 s in total with the final
  sources. At 8192 bits (589,793 clauses, 1.86 million hints), it converted in 2,322 s with a peak of
  50.2 GB, using the version before `reverse`, `clz` and `cpop`.
- Certificates: the largest certificate checked had 9.04 million hints (`x * (y * z) = (x * y) * z`
  at 7 bits). It took 2,052 s at 8.3 GB with an earlier version of the same checker. The LRAT file is
  parsed in memory by core's parser. A 75 MB LRAT file did not fit in 24 GB, and a 695 MB file did not
  fit in 40 GB.
- Split base check (Lean v4.35.0-rc4, four shards per fact): at 8192 bits, no process exceeded
  11.5 GB. At 16384 bits (1,179,617 clauses, 425,974 gates, 3.73 million hints), the bit-blaster
  declaration took 133 s. The peaks were 15.2 GB for the prep file, at most 21.4 GB per shard and
  17.0 GB for the final file. Because the bit-blaster's run is one declaration, its memory grows with
  the problem.

## Not supported

- RAT steps in the certificate. A certificate that needs them is rejected.
- Facts that `bv_decide` proves without a SAT call. There is no axiom to replace.
- Certificates whose LRAT file does not fit in memory when parsed (see Scale).
- Theorems that use a `bv_decide` axiom outside `unsat_of_verifyBVExpr_eq_true`. These are not
  rebuilt; they are reported as `BVS_USER_SKIP`.
- Replacing the original declarations. The rebuilt declarations are new constants, so declarations
  that refer to an original still depend on its native axiom.
- Gate-level structural hashing. The CNF can be larger than core's.
- Lean versions before v4.31.0 (see Requirements).

## Files

- `BVS/Blast.lean`: the bit-blaster (`blastBool`, `cnfOf`, `wfEs`).
- `BVS/Sound/`: its soundness proof. The modules are `Basic` (state invariant, gates), `Circuits`,
  `Bits` (bit lists and `BitVec`), `Shifts`, `Unary` (`reverse`, `clz`, `cpop`), `Expr`, and `CNF`
  (`unsat_of_cnf`).
- `BVS/LratBits.lean`, `BVS/LratBitsSound.lean`: clause semantics and bitmask unit propagation, with
  soundness.
- `BVS/Lrat/Trie.lean` (clause equality and a first chunked checker), `BVS/Lrat/Chain.lean` (the chunk
  checker `chkUR` over a lookup function, `ChainL`), `BVS/Lrat/LeafTree.lean` (the tree of gate
  descriptors and learned clauses).
- `BVS/Unsat.lean`: `check4` and `bvs_unsat4`. `BVS/SplitBase.lean`: the split base check and
  `bvs_unsat5`.
- `BVS/Driver/Core.lean`, `BVS/Driver/Select.lean`, `BVS/Driver/Split.lean`, `BVS/Driver/Group.lean`: the
  commands (compiled code, untrusted). `BVS/Tactic.lean`: the tactic `bv_kdecide`, and
  `BVS/Estimate.lean`: `bvs5_estimate` (both compiled code, untrusted).
- `Audit.lean`, `Examples/`, `prep/`, `scripts/shard.sh`.
