module

public import BVS.Driver.Split
public meta import BVS.Driver.Split
public import Lean
public meta import Lean

public meta section
/-!
# The `bv_kdecide` tactic

`bv_kdecide` proves the goals that `bv_decide` proves. Its proof is checked by Lean's kernel and
depends only on `propext`, `Classical.choice` and `Quot.sound`; it has no `bv_decide` axiom.

All of the work happens inside the tactic:

1. `bv_decide` (with the configuration given to `bv_kdecide`) runs on a copy of the goal, in a scope
   whose changes to the environment are discarded. Its proof ends in
   `Reflect.unsat_of_verifyBVExpr_eq_true E C ax`, where `E` is the reflected problem, `C` the LRAT
   certificate and `ax : verifyBVExpr E C = true` the native axiom. The tactic keeps the proof term
   and the value of `E`.
2. The environment is restored, so the native axiom, `C` and the other auxiliary definitions of
   `bv_decide` are not added (definitions or theorems of `bv_decide` that the rest of the proof uses
   are added again). The tactic defines `E` as `<decl>._bvk_<i>._bvs_E` and proves `E.Unsat` with the
   kernel route of `bvs4_kernelize` (`BVS.Driver.Core`): the kernel bit-blaster, CaDiCaL on its CNF,
   and the chunked LRAT check, one declaration per chunk. When the CNF has more than `bvs4.splitAbove`
   clauses, the base check is split as in `bvs6_prep` (`BVS.Driver.Split`): one declaration for the
   bit-blaster's run and one per segment of `bvs4.segment` nodes. The result is the theorem
   `<decl>._bvk_<i>.unsat`.
3. In the proof term of step 1, `unsat_of_verifyBVExpr_eq_true E C ax` is replaced by that theorem,
   and the goal is closed with the result. The tactic fails if the term still depends on a native
   axiom.

The tactic does not use `C`: the kernel route solves its own CNF, which differs from the CNF of
`bv_decide`. Compiled code (the SAT solver, the bit-blaster run that produces the data, the processing
of the certificate, the commands that build the terms) is untrusted; an error there makes the tactic
fail and cannot produce a theorem that the kernel has not checked.
-/
open Lean Meta Elab Tactic Std.Tactic.BVDecide

namespace BVS.KTactic

open BVS.Driver4 (logLine addDefn addTrueThm listE ltTy treeE hintsE stepsTy hintsTy solve prepare
  collectVerify stdAxioms)
open BVS.Driver6 (entTy entE esTy reflTrue boolTrueThm nSeg nSegOk esAfter nGates addThmTimed)

register_option bvs4.splitAbove : Nat := {
  defValue := 200000
  descr := "bv_kdecide: split the base check when the CNF has more clauses than this" }
register_option bvs4.segment : Nat := {
  defValue := 30000
  descr := "bv_kdecide: nodes per segment of the split base check" }
register_option bvs4.stats : Bool := {
  defValue := false
  descr := "bv_kdecide: report sizes, times and (on Linux) peak memory in an information message" }

/-- Linux: reset the peak resident set size of this process to its current value
(`/proc/self/clear_refs`); does nothing elsewhere. Used only for `bvs4.stats`. -/
def resetPeakRss : IO Unit := do
  try IO.FS.writeFile "/proc/self/clear_refs" "5" catch _ => pure ()

/-- Linux: the peak resident set size of this process in MiB since the last reset (`VmHWM`), or 0. -/
def peakRssMiB : IO Nat := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    for l in s.splitOn "\n" do
      if l.startsWith "VmHWM:" then
        let kib := l.toList.foldl (fun a c => if c.isDigit then a * 10 + (c.toNat - '0'.toNat) else a) 0
        return kib / 1024
    return 0
  catch _ => return 0

/-- Sizes and times (ms) of one kernel proof. -/
structure KStats where
  nodes : Nat := 0
  clauses : Nat := 0
  steps : Nat := 0
  hints : Nat := 0
  chunks : Nat := 0
  segments : Nat := 0
  solveMs : Nat := 0
  dataMs : Nat := 0
  baseMs : Nat := 0
  chunkMs : Nat := 0
  maxChunkMs : Nat := 0
  assembleMs : Nat := 0

def KStats.summary (s : KStats) : String :=
  s!"{s.nodes} nodes, {s.clauses} clauses, {s.steps} LRAT steps, {s.hints} hints, {s.chunks} chunks" ++
  (if s.segments > 0 then s!", split base check with {s.segments} segments" else "") ++
  s!"; SAT {s.solveMs} ms, data {s.dataMs} ms; kernel: base {s.baseMs} ms, chunks {s.chunkMs} ms " ++
  s!"(max {s.maxChunkMs} ms), assembly {s.assembleMs} ms"

/-- A file name stem for the solver files: the declaration name reduced to letters, digits and `_`. -/
def fileTag (base : Name) : IO String := do
  let cs := (base.toString.toList.filter fun c => c.isAlphanum || c == '_').take 60
  return s!"bvk_{String.join (cs.map Char.toString)}_{← IO.monoNanosNow}"

/-- The directory for the solver files: `bvs4.workdir` if set, else the system's temporary directory. -/
def solverDir : CoreM String := do
  let d := BVS.Driver4.bvs4.workdir.get (← getOptions)
  if d != "" then return d
  let (_, p) ← IO.FS.createTempFile
  IO.FS.removeFile p
  return (p.parent.getD ".").toString

/-- Prove `BVLogicalExpr.Unsat E` in the kernel, where `E` is a closed term (a constant) whose value
is `bv`. Adds the data definitions and the check theorems under `base`, then the theorem
`base.unsat : E.Unsat`; returns its name. -/
def proveUnsatOf (base : Name) (E : Expr) (bv : BVLogicalExpr) : MetaM (Name × KStats) := do
  let opts ← getOptions
  let chunk := max 1 (BVS.Driver4.bvs4.chunk.get opts)
  let maxH := max 1 (BVS.Driver4.bvs4.chunkHints.get opts)
  let lit := mkRawNatLit
  unless supportedBool bv do
    throwError "bv_kdecide: the problem uses an operation that the kernel bit-blaster does not support: {toString bv |>.take 300}"
  let t0 ← IO.monoMsNow
  let (bst, out) := blastBool St.empty bv
  let F := (cnfOf bst.es out).toArray
  let L := F.size
  logLine s!"{base}: {bst.n} nodes, CNF {L} clauses"
  let dir ← solverDir
  let tag ← fileTag base
  let proof ← withOptions (fun o => BVS.Driver4.bvs4.workdir.set o dir) do
    solve F tag (BVS.Driver4.bvs4.timeout.get opts)
  let acts ← match LRAT.parseLRATProof proof with
    | .ok a => pure a
    | .error e => throwError "bv_kdecide: LRAT parse error {e}"
  let prep ← match prepare F acts with
    | .ok p => pure p
    | .error e => throwError "bv_kdecide: {e}"
  let t1 ← IO.monoMsNow
  let N := L + prep.learned.size
  let mut st : KStats := { nodes := bst.n, clauses := L, steps := prep.learned.size,
                           hints := prep.hints.foldl (fun a h => a + h.length) 0, solveMs := t1 - t0 }
  -- the leaf tree: gate descriptors for the clauses `1 … L`, then the learned clauses
  let lv := (leavesOf bst.es out).toArray
  unless lv.size == L do throwError "bv_kdecide: leaf count mismatch"
  let mut mp : Std.HashMap Nat Leaf := {}
  for i in [0:L] do mp := mp.insert (i + 1) lv[i]!
  for i in [0:prep.learned.size] do mp := mp.insert (L + 1 + i) (.cl prep.learned[i]!)
  let D := Nat.log2 (N + 1) + (if 2 ^ Nat.log2 (N + 1) < N + 1 then 1 else 0)
  let H := 2 ^ D / 2
  addDefn (base ++ `_bvs_T) ltTy (treeE mp N D)
  let T := mkConst (base ++ `_bvs_T)
  -- the hint chunks: at most `chunk` steps and (unless a single step) at most `maxH` hints each
  let mut table : Array (Nat × Nat × Nat) := #[]   -- (index, first id, number of steps)
  let mut i := 0
  while i < prep.hints.size do
    let mut j := i
    let mut h := 0
    while j < prep.hints.size && j - i < chunk && (j == i || h + prep.hints[j]!.length ≤ maxH) do
      h := h + prep.hints[j]!.length
      j := j + 1
    let part := (prep.hints.extract i j).toList
    addDefn (base ++ Name.mkSimple s!"_bvs_s{table.size}") stepsTy (listE hintsTy (part.map hintsE))
    table := table.push (table.size, L + 1 + i, part.length)
    i := j
  let split := L > bvs4.splitAbove.get opts
  -- split base check: the segments of the entry list (segment `j`: nodes `1 + (j-1)·S …`, newest first)
  let n := bst.n
  let S := max 1 (bvs4.segment.get opts)
  let m := if split then (n - 1 + S - 1) / S else 0
  let mut segs : Array (Nat × Nat × Nat × Nat) := #[]   -- (bound, bound of the older segments, first key, leaves)
  let mut lo := 3
  for j in [1:m + 1] do
    let b := min (1 + j * S) n
    let bprev := 1 + (j - 1) * S
    let seg := (bst.es.drop (n - b)).take (b - bprev)
    unless seg.length == b - bprev do
      throwError "bv_kdecide: segment {j} has {seg.length} entries, expected {b - bprev}"
    addDefn (nSeg base j) esTy (listE entTy (seg.map entE))
    let len := 3 * nGates seg
    segs := segs.push (b, bprev, lo, len)
    lo := lo + len
  let lenG := lo - 3
  if split then
    unless lenG + 2 == L do throwError "bv_kdecide: {lenG} gate leaves and 2, but {L} clauses"
  let t2 ← IO.monoMsNow
  st := { st with chunks := table.size, segments := m, dataMs := t2 - t1 }
  logLine s!"{base}: {st.steps} steps, {st.hints} hints, {table.size} chunks, {m} segments; SAT {st.solveMs} ms"
  -- kernel: the base check
  if split then
    let ms ← addThmTimed (base ++ `_bvs_blast)
      (boolTrueThm (mkApp4 (mkConst ``BVS.blastCk) E (esAfter base m) (lit n) (lit out))) reflTrue
    logLine s!"{base}: bit-blaster run {ms} ms"
    for j in [1:m + 1] do
      let (b, bprev, key, len) := segs[j - 1]!
      let ms ← addThmTimed (nSegOk base j) (boolTrueThm (mkAppN (mkConst ``BVS.segOK)
        #[T, lit D, lit key, mkConst (nSeg base j), lit b, lit bprev, lit len])) reflTrue
      logLine s!"{base}: segment {j} ({len} leaves) {ms} ms"
  else
    let ms ← addTrueThm (base ++ `_bvs_base) (mkApp5 (mkConst ``BVS.check4) E T (lit D) (lit H) (lit L))
    logLine s!"{base}: base check {ms} ms"
  let t3 ← IO.monoMsNow
  st := { st with baseMs := t3 - t2 }
  -- kernel: the chunks
  let lookE := mkApp2 (mkConst ``BVS.look4) T (lit H)
  let mut chain : Option Expr := none
  let mut cur := L + 1
  for (k, s, cnt) in table do
    let nm := base ++ Name.mkSimple s!"_bvs_s{k}"
    let thm := base ++ Name.mkSimple s!"_bvs_s{k}_ok"
    let ms ← addTrueThm thm (mkApp3 (mkConst ``BVS.chkUR) lookE (lit s) (mkConst nm))
    st := { st with chunkMs := st.chunkMs + ms, maxChunkMs := max st.maxChunkMs ms }
    logLine s!"{base}: chunk {k} ({cnt} steps from id {s}) {ms} ms"
    let c := mkApp4 (mkConst ``BVS.chkUR_sound) lookE (mkConst nm) (lit s) (mkConst thm)
    let e := s + cnt
    chain := some <| match chain with
      | none => c
      | some ch => mkApp6 (mkConst ``BVS.ChainL.trans) lookE (lit (L + 1)) (lit cur) (lit e) ch c
    cur := e
  let some ch := chain | throwError "bv_kdecide: the certificate has no steps"
  let t4 ← IO.monoMsNow
  discard <| addTrueThm (base ++ `_bvs_empty) (mkApp4 (mkConst ``BVS.stepEmpty4) T (lit D) (lit H) (lit N))
  -- assembly
  let pf ← if split then do
      let mut acc := mkApp3 (mkConst ``BVS.entsOK_nil) T (lit H) (lit 1)
      let mut lenR := 0
      for j in [1:m + 1] do
        let (b, bprev, key, len) := segs[j - 1]!
        acc := mkAppN (mkConst ``BVS.acc_step) #[T, lit D, lit H, reflTrue, mkConst (nSeg base j),
          esAfter base (j - 1), lit b, lit bprev, lit lenR, lit len, lit key, reflTrue, acc, mkConst (nSegOk base j)]
        lenR := lenR + len
      pure <| mkAppN (mkConst ``BVS.bvs_unsat5) #[E, T, lit D, lit H, lit L, lit N, lit n, lit out, lit lenG,
        esAfter base m, mkConst (base ++ `_bvs_blast), reflTrue, acc, reflTrue, reflTrue, ch,
        mkConst (base ++ `_bvs_empty)]
    else
      pure <| mkAppN (mkConst ``BVS.bvs_unsat4) #[E, T, lit D, lit H, lit L, lit N,
        mkConst (base ++ `_bvs_base), ch, mkConst (base ++ `_bvs_empty)]
  let fact := base ++ `unsat
  discard <| addThmTimed fact (mkApp (mkConst ``BVLogicalExpr.Unsat) E) pf
  st := { st with assembleMs := (← IO.monoMsNow) - t4 }
  return (fact, st)

/-! ## Running `bv_decide` -/

/-- What the tactic keeps from a run of `bv_decide` on a copy of the goal. -/
structure BvdRun where
  /-- the proof term of `bv_decide` -/
  proof : Expr
  /-- for each `unsat_of_verifyBVExpr_eq_true E C ax` in `proof`: the subterm, the value of `E` (a
  closed term) and its compiled evaluation -/
  facts : Array (Expr × Expr × BVLogicalExpr)
  /-- the constants that stand for `E` in these subterms (`bv_decide`'s `_expr_def` definitions) -/
  exprDefs : NameSet
  /-- the declarations that `bv_decide` added and that the rest of `proof` uses, dependencies first -/
  extra : Array ConstantInfo
  /-- time of the `bv_decide` run (ms) -/
  ms : Nat
  /-- peak resident set size of the process during the `bv_decide` run (MiB; only with `bvs4.stats`) -/
  peakMiB : Nat := 0

/-- Post-order collection of the constants of `c`'s dependency graph that are not in `env0` and not in
`skip` (looked up in `env`). -/
partial def newDeps (env0 env : Environment) (skip : NameSet) (c : Name) (st : NameSet × Array ConstantInfo) :
    MetaM (NameSet × Array ConstantInfo) := do
  if st.1.contains c || env0.contains c || skip.contains c then return st
  let some ci := env.find? c | throwError "bv_kdecide: unknown constant {c} in the proof of bv_decide"
  let mut st := (st.1.insert c, st.2)
  let deps := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
  for d in deps do st ← newDeps env0 env skip d st
  return (st.1, st.2.push ci)

/-- The compiled evaluation of `E : BVLogicalExpr` (a constant of `bv_decide`), or else of its value. -/
def evalBV (E val : Expr) : MetaM BVLogicalExpr := do
  try
    unsafe evalExpr BVLogicalExpr (mkConst ``BVLogicalExpr) E
  catch _ =>
    withOptions (fun o => o.set `compiler.extract_closed false) <|
      unsafe evalExpr BVLogicalExpr (mkConst ``BVLogicalExpr) val

/-- Run `bv_decide` with configuration `cfg` on a copy of goal `g`; discards its changes to the
environment. -/
def runBvDecide (g : MVarId) (cfg : TSyntax ``Lean.Parser.Tactic.optConfig) : TacticM BvdRun :=
  g.withContext do
  let env0 ← getEnv
  let stats := bvs4.stats.get (← getOptions)
  if stats then resetPeakRss
  let t0 ← IO.monoMsNow
  withoutModifyingEnv do
    let g' ← mkFreshExprMVar (← instantiateMVars (← g.getType)) (kind := .syntheticOpaque)
    let gs ← Tactic.run g'.mvarId! (evalTactic (← `(tactic| bv_decide $cfg)))
    unless gs.isEmpty do throwError "bv_kdecide: bv_decide left {gs.length} goals"
    let proof ← instantiateMVars g'
    if proof.hasMVar then throwError "bv_kdecide: the proof term of bv_decide contains metavariables"
    let ms := (← IO.monoMsNow) - t0
    let peakMiB ← if stats then peakRssMiB else pure 0
    let apps := collectVerify proof
    let mut facts : Array (Expr × Expr × BVLogicalExpr) := #[]
    let mut exprDefs : NameSet := {}
    for app in apps do
      if facts.any (·.1 == app) then continue
      let E := app.getArg! 0
      let mut val := E
      if let .const n _ := E then
        exprDefs := exprDefs.insert n
        let some v := (← getConstInfo n).value? | throwError "bv_kdecide: {n} has no value"
        val := v
      let bv ← evalBV E val
      facts := facts.push (app, val, bv)
    -- the declarations of `bv_decide` that the rest of the proof uses
    let rest := proof.replace fun e => if apps.contains e then some (mkConst ``True) else none
    let env ← getEnv
    let mut st : NameSet × Array ConstantInfo := ({}, #[])
    for c in rest.getUsedConstants do st ← newDeps env0 env exprDefs c st
    for ci in st.2 do
      if ci matches .axiomInfo _ then
        throwError "bv_kdecide: the proof of bv_decide uses the axiom {ci.name} outside `unsat_of_verifyBVExpr_eq_true`"
    return { proof, facts, exprDefs, extra := st.2, ms, peakMiB }

/-! ## Axioms -/

/-- Axioms that stand for compiled evaluation. -/
def isNativeAxiom (n : Name) : Bool :=
  n == `Lean.ofReduceBool || n == `Lean.ofReduceNat || n == `Lean.trustCompiler ||
  n.components.contains `_native

/-- The axioms that the constants in `roots` depend on, not looking into the constants in `skip`. -/
def axiomsOf (roots : Array Name) (skip : NameSet := {}) : CoreM NameSet := do
  let env ← getEnv
  let mut seen : NameSet := skip
  let mut axs : NameSet := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    match env.find? c with
    | some (.axiomInfo _) => axs := axs.insert c
    | some ci =>
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
      if let .inductInfo iv := ci then todo := todo ++ iv.ctors.toArray
    | none => pure ()
  return axs

/-! ## The tactic -/

def addAgain (ci : ConstantInfo) : CoreM Unit :=
  withOptions (fun o => o.set `Elab.async false) do
  match ci with
  | .defnInfo d => addDecl (.defnDecl d)
  | .thmInfo t => addDecl (.thmDecl t)
  | .opaqueInfo o => addDecl (.opaqueDecl o)
  | _ => throwError "bv_kdecide: cannot add {ci.name} from the proof of bv_decide again"

/-- Add again the declarations of `bv_decide` that the rest of its proof uses. Some of them are not
named after the current declaration (for example `T.enumToBitVec` for an enumeration type `T`), and
`bv_decide`'s preprocessing creates them through Lean's mechanism for such shared declarations, which a
plain `addDecl` cannot use. So first the preprocessing alone (`bv_normalize`) runs on another copy of
the goal, with its changes to the environment kept; the declarations it creates are then present and
are not added again. -/
def addExtras (g : MVarId) (cfg : TSyntax ``Lean.Parser.Tactic.optConfig) (extra : Array ConstantInfo) :
    TacticM Unit := g.withContext do
  if extra.isEmpty then return
  let env ← getEnv
  if extra.any (fun ci => !env.contains ci.name) then
    let g' ← mkFreshExprMVar (← instantiateMVars (← g.getType)) (kind := .syntheticOpaque)
    try discard <| Tactic.run g'.mvarId! (evalTactic (← `(tactic| bv_normalize $cfg)))
    catch _ => pure ()
  for ci in extra do
    unless (← getEnv).contains ci.name do
      try addAgain ci
      catch ex => throwError "bv_kdecide: the proof of bv_decide uses {ci.name}, which bv_decide created and which cannot be added again here: {ex.toMessageData}"

/-- Close goal `g` like `bv_decide` (configuration `cfg`), with a kernel-checked proof. -/
def bvKDecideGoal (g : MVarId) (cfg : TSyntax ``Lean.Parser.Tactic.optConfig) : TacticM Unit := g.withContext do
  let t0 ← IO.monoMsNow
  let run ← runBvDecide g cfg
  let env1 ← getEnv
  let statsOn := bvs4.stats.get (← getOptions)
  if statsOn then resetPeakRss
  -- The kernel route runs without a heartbeat limit: neither the elaborator's limit nor the kernel's
  -- (which reads the option `maxHeartbeats`) applies to it, and the heartbeat counter is restored
  -- afterwards, so that its work does not count against the rest of the declaration. Its data are long
  -- lists, so the recursion limit is raised as in the shard files of `bvs6_prep` (1000000).
  let hb ← IO.getNumHeartbeats
  let recDepth := max 1000000 (maxRecDepth.get (← getOptions))
  try
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 0, maxRecDepth := recDepth }) do
    withOptions (fun o => maxRecDepth.set (maxHeartbeats.set o 0) recDepth) do
    addExtras g cfg run.extra
    let mut repl : Std.HashMap Expr Expr := {}
    let mut constRepl : NameMap Name := {}
    let mut stats : Array String := #[]
    let mut factNames : NameSet := {}
    for (app, val, bv) in run.facts do
      -- a fresh prefix: the name generator can return a name again when nothing was declared under
      -- exactly that name (for example in two tactic blocks of one declaration under `Elab.async false`)
      let base0 ← Term.mkAuxName `_bvk
      let mut base := base0
      let mut k := 1
      while (← getEnv).contains (base ++ `_bvs_E) do
        k := k + 1
        base := base0.appendIndexAfter k
      let eName := base ++ `_bvs_E
      addDefn eName (mkConst ``BVLogicalExpr) val
      let (fact, st) ← proveUnsatOf base (mkConst eName) bv
      let fax ← collectAxioms fact
      unless fax.all stdAxioms.contains do
        throwError "bv_kdecide: internal error: {fact} depends on the axioms {fax.toList}"
      factNames := factNames.insert fact
      repl := repl.insert app (mkConst fact)
      if let .const n _ := app.getArg! 0 then constRepl := constRepl.insert n eName
      stats := stats.push st.summary
    let proof := run.proof.replace fun e =>
      match repl.get? e with
      | some r => some r
      | none => match e with
        | .const n ls => (constRepl.find? n).map (mkConst · ls)
        | _ => none
    let env ← getEnv
    for c in proof.getUsedConstants do
      unless env.contains c do
        throwError "bv_kdecide: internal error: the proof refers to {c}, which is not in the environment"
    -- no native axiom, except those that the statement itself depends on
    let ty ← instantiateMVars (← g.getType)
    let mut stmt := ty.getUsedConstants
    for d in (← getLCtx) do
      unless d.isImplementationDetail do stmt := stmt ++ (← instantiateMVars d.type).getUsedConstants
    let allowed := (← axiomsOf stmt).toList.filter isNativeAxiom
    let native := (← axiomsOf proof.getUsedConstants factNames).toList.filter fun a =>
      isNativeAxiom a && !allowed.contains a
    unless native.isEmpty do
      throwError "bv_kdecide: the proof still depends on the native axioms {native}"
    g.assign proof
    if statsOn then
      let msg := if stats.isEmpty then "closed by the preprocessing of bv_decide (no SAT call)"
        else String.intercalate "; " stats.toList
      let decl := (← Term.getDeclName?).getD .anonymous
      let line := s!"bv_kdecide [{decl}]: bv_decide {run.ms} ms; {msg}; total {(← IO.monoMsNow) - t0} ms; " ++
        s!"peak RSS: bv_decide {run.peakMiB} MiB, kernel route {← peakRssMiB} MiB"
      logLine line
      logInfo line
  catch ex =>
    setEnv env1
    throw ex
  finally
    IO.setNumHeartbeats hb

/--
`bv_kdecide` proves the goals that `bv_decide` proves, with a proof that Lean's kernel checks: the
proof depends only on `propext`, `Classical.choice` and `Quot.sound`, not on a `bv_decide` axiom.

It accepts the configuration of `bv_decide` (`bv_kdecide (config := { timeout := 60 })`,
`bv_kdecide +acNf`) and passes it on: `bv_decide` runs first, on a copy of the goal, and the problem it
reflects is then proved unsatisfiable by the kernel route of `bvs4_kernelize`. Options:
`bvs4.timeout` (SAT time limit of the kernel route, seconds), `bvs4.chunk`, `bvs4.chunkHints`,
`bvs4.splitAbove`, `bvs4.segment`, `bvs4.workdir`, `bvs4.cadical`, `bvs4.log`, `bvs4.stats`. The kernel
checks run without a heartbeat limit, do not count against `maxHeartbeats`, and run with `maxRecDepth`
at least 1000000.
-/
syntax (name := bvKDecide) "bv_kdecide" Lean.Parser.Tactic.optConfig : tactic

@[tactic bvKDecide] def evalBvKDecide : Tactic := fun stx => do
  let cfg : TSyntax ``Lean.Parser.Tactic.optConfig := ⟨stx[1]⟩
  let g ← getMainGoal
  bvKDecideGoal g cfg
  replaceMainGoal []

end BVS.KTactic
