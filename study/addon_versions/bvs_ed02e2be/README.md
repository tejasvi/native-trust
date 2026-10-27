# bvs: kernel-checked re-proofs of `bv_decide` facts

`bv_decide` proves a goal about bit vectors by reducing it to the unsatisfiability of a formula
`E : Std.Tactic.BVDecide.BVLogicalExpr` and closing it with
`Std.Tactic.BVDecide.Reflect.unsat_of_verifyBVExpr_eq_true E C h`. Here `C` is an LRAT certificate
from a SAT solver, and `h : verifyBVExpr E C = true` is established by compiled (native) evaluation.
In the Lean versions this package was tested with, `h` is an auxiliary axiom named
`…._native.bv_decide.ax_…`.

This package proves `Std.Tactic.BVDecide.BVLogicalExpr.Unsat E` in Lean's kernel, without native
evaluation. It then adds a copy of the original theorem in which `unsat_of_verifyBVExpr_eq_true E C h`
is replaced by that proof. The copy has the same statement as the original. It depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`. The original theorem is not changed, and other
declarations that refer to it still depend on the native axiom.

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

Lean's kernel checks the theorems. The checks are evaluations of Boolean functions by the kernel.
These functions compute with natural numbers, and for `Nat` addition, subtraction, multiplication,
division, modulo, comparison, bitwise operations and shifts the kernel uses its built-in
arbitrary-precision (GMP) implementations. These implementations are part of the trusted base. The
proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`; they do not use
`Lean.ofReduceBool` or `Lean.trustCompiler`.

The following parts are untrusted:

- the SAT solver;
- the compiled bit-blasting that produces the data;
- the processing of the certificate (trimming, renumbering, hint annotation);
- the commands that build the proof terms.

An error in these parts can make a conversion fail. It cannot produce a theorem that the kernel has not
checked.

## Requirements

- Lean 4. `lean-toolchain` selects v4.35.0. The package was also built on v4.31.0, v4.32.2, v4.33.1,
  v4.34.1, v4.35.0-rc4 and v4.36.0-rc1; on each of them the audit file showed only the standard axioms
  and all examples re-proved. On v4.30.0 a proof script in `BVS/Sound/Expr.lean` fails. Versions up to
  v4.29 lack `Std.Tactic.BVDecide.BVUnOp.cpop`.
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

A prep file names the facts. Compiling it runs the solver, defines the data, proves the base check
and writes `k` shard files and a final file into a directory. The shard files contain the chunk
theorems and can be compiled in parallel. The final file imports the shards, assembles the theorems
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
shared Linux server. They include importing the libraries and running core's `bv_decide`, unless
stated otherwise. Memory figures are peak resident set sizes. The server was shared with other jobs,
and repeated runs varied by up to about 20%.

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

These runs used the version of the sources before `reverse`, `clz` and `cpop` were added. A rerun of
w = 4 to 256 with the final sources gave the same CNF and certificate sizes. The bit-blaster does not
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
  17.0 GB for the final file. The bit-blaster's run is one declaration, and its memory grows with the
  problem.

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
  commands (compiled code, untrusted).
- `Audit.lean`, `Examples/`, `prep/`, `scripts/shard.sh`.
