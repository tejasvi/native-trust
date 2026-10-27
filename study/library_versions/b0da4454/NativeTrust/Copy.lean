import Lean
import NativeTrust.Basic

/-!
# Kernel-reducible copies of definitions

`kernelCopy e` returns an expression `e'` that is definitionally equal to `e` but that the kernel
can evaluate, and evaluate faster:

* every definition reachable from `e` whose body (transitively) uses `WellFounded.fix` is
  replaced by a copy in which `WellFounded.fix` is `NativeTrust.wfFix`;
* with `opt` (experimental, off by default), every reachable definition is copied with small non-recursive
  definitions inlined into its body: instances, structure projections, matchers, `casesOn`,
  recursion functionals and wrappers such as `ite`, `bne` or `Nat.decEq`. In Lean 4.35
  `Decidable` is a structure and `ite` is `Bool.casesOn` on its `decide` field, so an `if a < b`
  on `Nat` becomes `Bool.rec … (Nat.ble (a+1) b)`, which the kernel evaluates with its built-in
  arithmetic. This is what hand-written "kernel-form" checkers do, done definitionally.

Copies keep the original type, level parameters and reducibility hints. Each copy is obtained
from its original by unfolding definitions and by changing well-foundedness proofs, so the
kernel accepts `c = c'` by `rfl` (delta reduction plus proof irrelevance); `e = e'` is likewise
checked by `rfl` and no new axiom is involved. The kernel's built-in `Nat` operations are never
inlined.

Names: at command level copies are named `_kt.<module>.<original>`, so two modules never declare
the same name, and they are recorded in an environment extension so that later commands and
modules reuse them. Inside an asynchronously elaborated proof Lean only accepts declarations under
the current declaration's name, so there copies are named `<decl>._kt.<original>` and stay local.
-/

open Lean Meta

namespace NativeTrust

/-- Constants replaced unconditionally by kernel-reducible ones, with the equation
`@orig = @replacement`: `WellFounded.fix` by its fuel version `fixFuel` (equal by a proof from
`WellFounded.fix_eq`, bridged by congruence; durable beyond Lean 4.36). -/
def baseReplacements : List (Name × Name) :=
  [(``WellFounded.fix, ``NativeTrust.fixFuel)]

def baseEquations : List (Name × Name) :=
  [(``WellFounded.fix, ``NativeTrust.fix_eq_fixFuel)]

/-- The `accGen` variant (`WellFounded.fix` ↦ `wfFix`, equal by `rfl`; Lean ≤ 4.36 only), kept for
comparison (`CopyConfig.wfAcc`). -/
def accReplacements : List (Name × Name) :=
  [(``WellFounded.fix, ``NativeTrust.wfFix)]

def accEquations : List (Name × Name) :=
  [(``WellFounded.fix, ``NativeTrust.fix_eq_wfFix)]

/-- A kernel-reducible copy `copy` of a constant, with `eq : @orig = @copy` (proved by `rfl`). -/
structure CopyEntry where
  orig : Name
  copy : Name
  eq : Name
  deriving Inhabited

/-- Registry of copies made at command level, shared with later commands and modules. -/
initialize copyExt : SimplePersistentEnvExtension CopyEntry (NameMap CopyEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m e => m.insert e.orig e
    addImportedFn := fun arrs =>
      arrs.foldl (fun m arr => arr.foldl (fun m e => m.insert e.orig e) m) {}
  }

/-- Proof-carrying replacements registered with `@[kernel_replace]`: `f ↦ (g, thm)` with
`thm : @f = @g`. Kernel evaluation uses `g`; results are bridged back to `f` by congruence, so
`g` may differ from `f` arbitrarily as long as the equation is proved. -/
initialize kernelReplaceExt :
    SimpleScopedEnvExtension (Name × Name × Name) (NameMap (Name × Name)) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun m (f, g, thm) => m.insert f (g, thm)
  }

/-- `@[kernel_replace] theorem thm : @f = @g` registers `g` as a kernel-friendly replacement
for `f` (e.g. a fuel-based or kernel-form version proved equal to it). -/
initialize registerBuiltinAttribute {
    name := `kernel_replace
    descr := "proof-carrying replacement used by NativeTrust's kernel evaluation"
    add := fun decl _ kind => do
      let info ← getConstInfo decl
      unless info matches .thmInfo _ do
        throwError "@[kernel_replace]: `{decl}` must be a theorem `@f = @g`"
      match info.type.eq? with
      | some (_, .const f us, .const g vs) =>
        unless us == vs && us.all Level.isParam do
          throwError "@[kernel_replace]: both sides must be the same universe-polymorphic constants"
        kernelReplaceExt.add (f, g, decl) kind
      | _ => throwError "@[kernel_replace]: the statement must be `@f = @g` for constants f, g"
  }

/-- Print a line to the process's standard error, bypassing the elaborator's capture of `IO` output
(which turns it into messages, printed only when the command ends): drivers keep these lines even
when the process is stopped later. Opens the file in append mode, so a log shared with standard
output is not truncated. -/
def eprintRaw (s : String) : IO Unit := do
  try
    let h ← IO.FS.Handle.mk "/dev/stderr" .append
    h.putStrLn s
    h.flush
  catch _ => pure ()

structure CopyConfig where
  /-- Replace `WellFounded.fix` by a kernel-reducible version: `fixFuel` (default; durable) or,
  with `wfAcc`, the accessibility-generator `wfFix` (Lean ≤ 4.36 only). -/
  wf : Bool := true
  /-- Use `wfFix` (`accGen`, equal by `rfl`) instead of `fixFuel`. -/
  wfAcc : Bool := false
  /-- Copy every reachable definition with small definitions inlined (experimental). -/
  opt : Bool := false
  /-- Largest definition body (in expression nodes) that is inlined. -/
  inlineSize : Nat := 256
  /-- Inlining depth limit. -/
  inlineDepth : Nat := 64
  /-- Print each copy and the kernel time of its equation to standard error. -/
  trace : Bool := false
  /-- Heartbeat limit (thousands) for the kernel check of a copy's equation (congruence, then the
  `rfl` fallback); `0` = no limit. -/
  rflHeartbeats : Nat := 20000

/-- The kernel evaluates these with GMP arithmetic; they must stay as they are. -/
def kernelPrimitives : List Name :=
  [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.gcd, ``Nat.beq, ``Nat.ble,
   ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``Nat.pow, ``Nat.log2,
   ``Nat.succ, ``Nat.zero]

/-- Never copied: copying cannot make them evaluable (their value depends on a classical test of
well-foundedness), and keeping the original names lets diagnostics recognise them. -/
def uncopyable : List Name :=
  [`WellFounded.extrinsicFix, `WellFounded.extrinsicFix₂, `WellFounded.extrinsicFix₃]

/-- Number of nodes of `e` (without sharing), counting up to `limit`. -/
partial def sizeUpTo (limit : Nat) (e : Expr) : Nat :=
  go e 0
where
  go (e : Expr) (n : Nat) : Nat :=
    if n ≥ limit then n else
    match e with
    | .app f a => go a (go f (n + 1))
    | .lam _ t b _ | .forallE _ t b _ => go b (go t (n + 1))
    | .letE _ t v b _ => go b (go v (go t (n + 1)))
    | .mdata _ b | .proj _ _ b => go b (n + 1)
    | _ => n + 1

/-- Is this the entry point of a recursive function (its body runs the recursion)? -/
def isRecursiveBody (e : Expr) : Bool :=
  (e.find? fun
    | .const n _ =>
      n == ``WellFounded.fix || n == ``NativeTrust.wfFix || n == ``NativeTrust.fixFuel ||
      n == `WellFounded.Nat.fix ||
      n == `WellFounded.extrinsicFix || n == `WellFounded.extrinsicFix₂ ||
      n == `WellFounded.extrinsicFix₃ ||
      (match n with | .str _ s => s == "brecOn" || s == "binductionOn" | _ => false)
    | _ => false).isSome

/-- Small non-recursive definitions are inlined into copies. -/
def isInlinable (env : Environment) (cfg : CopyConfig) (c : Name) : Bool :=
  -- constants that are replaced must survive until `substConsts` sees them
  if kernelPrimitives.contains c || baseReplacements.any (·.1 == c) then false else
  match env.find? c with
  | some (.defnInfo d) =>
    d.safety == .safe && !isRecursiveBody d.value && sizeUpTo (cfg.inlineSize + 1) d.value ≤ cfg.inlineSize
  | _ => false

/-- Reduce `proj S i (C params fields)` to the field. -/
def reduceProjCtor? (env : Environment) (i : Nat) (s : Expr) : Option Expr :=
  match s.getAppFn with
  | .const c _ => match env.find? c with
    | some (.ctorInfo info) =>
      let args := s.getAppArgs
      if info.numParams + i < args.size then some args[info.numParams + i]! else none
    | _ => none
  | _ => none

/-- For each parameter of constant `c`: is it computationally irrelevant (a proof or a type
former)? Such arguments are never evaluated, so `inlineSimp` leaves them untouched. -/
def irrelevantArgs (c : Name) : MetaM (Array Bool) := do
  let some ci := (← getEnv).find? c | return #[]
  try
    forallTelescope ci.type fun xs _ => xs.mapM fun x => do
      let t ← inferType x
      return (← isProp t) || (← isTypeFormerType t)
  catch _ => return #[]

/-- Inline small definitions (see `isInlinable`) at application heads, and reduce the beta
redexes and projections of constructors that this exposes. Proofs and types (binder types,
motives, proof arguments, proof fields of structures) are left untouched: they are never
evaluated, and rewriting them would only make the copy harder to relate to its original. The
result is definitionally equal to the input. -/
partial def inlineSimp (env : Environment) (cfg : CopyConfig) (e : Expr) : MetaM Expr := do
  let maskCache ← IO.mkRef ({} : Std.HashMap Name (Array Bool))
  let mask (c : Name) : MetaM (Array Bool) := do
    if let some m := (← maskCache.get)[c]? then return m
    let m ← irrelevantArgs c
    maskCache.modify (·.insert c m)
    return m
  let cache ← IO.mkRef ({} : Std.HashMap (Nat × Expr) Expr)
  let rec go (depth : Nat) (e : Expr) : MetaM Expr := do
    if let some r := (← cache.get)[(depth, e)]? then return r
    let r ← match e with
      | .app .. => do
        let f := e.getAppFn
        let args := e.getAppArgs
        match f with
        | .const c us =>
          let m ← mask c
          let args ← args.mapIdxM fun i a => if m.getD i false then pure a else go depth a
          if depth < cfg.inlineDepth && isInlinable env cfg c then
            let v := (env.find? c).get!.instantiateValueLevelParams! us
            go (depth + 1) (v.beta args)
          else pure (mkAppN f args)
        | .lam .. => go depth (f.beta args)
        | _ => pure (mkAppN (← go depth f) (← args.mapM (go depth)))
      | .const c us =>
        -- an unapplied instance, e.g. `instAddNat`, becomes its structure literal
        if depth < cfg.inlineDepth && isInlinable env cfg c then
          let v := (env.find? c).get!.instantiateValueLevelParams! us
          if v.isLambda then pure e else go (depth + 1) v
        else pure e
      | .proj S i s => do
        -- proof fields (e.g. `Decidable.reflects_decide`) stay as they are
        let isProofField ← match env.find? S with
          | some (.inductInfo { ctors := [ctor], numParams, .. }) =>
            pure ((← mask ctor).getD (numParams + i) false)
          | _ => pure false
        if isProofField then pure e else
        let s ← go depth s
        match reduceProjCtor? env i s with
        | some fld => go depth fld
        | none => pure (.proj S i s)
      | .lam n t b bi => return .lam n t (← go depth b) bi
      | .letE n t v b nd => return .letE n t (← go depth v) (← go depth b) nd
      | .mdata m b => return .mdata m (← go depth b)
      | _ => pure e
    cache.modify (·.insert (depth, e) r)
    return r
  go 0 e

structure CopyState where
  /-- Memo: does this constant need a copy? -/
  needs : Std.HashMap Name Bool := {}
  /-- Original ↦ replacement, for base replacements and copies. -/
  subst : NameMap Name := {}
  /-- Original ↦ theorem `@orig = @copy`, for copies. -/
  eqs : NameMap Name := {}
  /-- Constants whose copy the kernel did not accept as `rfl`-equal (kept as they are). -/
  failed : NameSet := {}
  /-- Copies created by this run, in dependency order. -/
  created : Array Name := #[]
  /-- Kernel time (ms) to check each copy and its equation, and whether the equation was proved by
  congruence (otherwise by `rfl`). -/
  timings : Array (Name × Nat × Nat × Bool) := #[]
  /-- Last kernel error of a congruence equation (diagnostics). -/
  lastCongrError : Option MessageData := none

abbrev CopyM := ReaderT CopyConfig (StateRefT CopyState MetaM)

/-- Prefix for copies made here: `<decl>._kt` inside an asynchronous proof branch, otherwise
`_kt.<module>`. -/
def copyPrefix (wfAcc : Bool := false) : CoreM Name := do
  let env ← getEnv
  -- copies made with the accessibility-generator route get their own names: they must never be
  -- mixed with fuel copies (their equations hold by `rfl` only among themselves)
  let tag := if wfAcc then `_kta else `_kt
  match env.asyncPrefix? with
  | some p => return p ++ tag
  | none => return tag ++ env.mainModule

/-- The copy registry may only be extended outside asynchronous branches. -/
def canRegister : CoreM Bool :=
  return (← getEnv).asyncPrefix?.isNone

def CopyState.init (env : Environment) (wf : Bool := true) (wfAcc : Bool := false) : CopyState :=
  -- the shared registry holds fuel copies; the accessibility-generator route starts afresh
  let reg := if wfAcc then {} else copyExt.getState env
  let user := kernelReplaceExt.getState env
  let subst := reg.foldl (fun m o e => m.insert o e.copy) {}
  let eqs := reg.foldl (fun m o e => m.insert o e.eq) {}
  let subst := user.foldl (fun m f (g, _) => m.insert f g) subst
  let eqs := user.foldl (fun m f (_, thm) => m.insert f thm) eqs
  let (reps, reqs) := if wfAcc then (accReplacements, accEquations) else (baseReplacements, baseEquations)
  let subst := if wf then reps.foldl (fun m (a, b) => m.insert a b) subst else subst
  let eqs := if wf then reqs.foldl (fun m (a, b) => m.insert a b) eqs else eqs
  { subst, eqs }

/-- Does constant `c` need a copy? Without `opt`: when evaluating it reaches a replaced constant.
With `opt`: every safe definition that is not inlined and not a kernel primitive. Only
definition bodies are followed: theorems are never evaluated, and opaque constants cannot be. -/
partial def needsCopy (c : Name) : CopyM Bool := do
  if (← get).subst.contains c then return true
  if (← get).failed.contains c then return false
  if let some b := (← get).needs[c]? then return b
  -- provisional answer, in case of (impossible in the kernel) cycles
  modify fun s => { s with needs := s.needs.insert c false }
  let cfg ← read
  let env ← getEnv
  let r ← match env.find? c with
    | some (.defnInfo d) =>
      if d.safety != .safe || kernelPrimitives.contains c || uncopyable.contains c then pure false
      else if cfg.opt && d.value.isLambda && !isInlinable env cfg c then
        -- functions only: data tables are not worth copying (and are expensive to re-check)
        let body ← inlineSimp env cfg d.value
        if body != d.value then pure true else body.getUsedConstants.anyM needsCopy
      else d.value.getUsedConstants.anyM needsCopy
    | _ => pure false
  modify fun s => { s with needs := s.needs.insert c r }
  return r

def substConsts (subst : NameMap Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => (subst.find? n).map (mkConst · ls)
    | _ => none

/-- Add a declaration with the kernel checking it synchronously. -/
def addDeclSync (decl : Declaration) : CoreM Unit :=
  withOptions (Elab.async.set · false) do addDecl decl

/-- Distinct occurrences `c.{us}` in `e` of the constants in `names`. -/
partial def collectOccs (names : NameMap α) (e : Expr) : Std.HashSet (Name × List Level) :=
  (go e).run ({}, {}) |>.run.2.1
where
  go (e : Expr) : StateT (Std.HashSet (Name × List Level) × Std.HashSet Expr) Id Unit := do
    if (← get).2.contains e then return
    modify fun (o, v) => (o, v.insert e)
    match e with
    | .const c us => if names.contains c then modify fun (o, v) => (o.insert (c, us), v)
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()

/-- A proof of `e = e[cᵢ ↦ cᵢ']` from equations `hᵢ : @cᵢ = @cᵢ'` (`eqs` maps `cᵢ` to
`(cᵢ', hᵢ)`), by congruence: `e` is `M c₁ … cₖ` for the motive `M` that abstracts the occurrences.
`type` is the type of `e` (closed). The term is built without elaborator checks: the kernel checks
it, and callers fall back to `rfl` if it does not accept it (e.g. when `M` is not type correct).
This way the kernel never compares two closed terms that differ only in copies, which could make
it unfold recursive functions applied to literals. -/
def congrSubst (e type : Expr) (eqs : NameMap (Name × Name)) : MetaM (Option Expr) := do
  let occs := (collectOccs eqs e).toArray
  if occs.isEmpty then return none
  let env ← getEnv
  let types ← occs.mapM fun (c, us) => do
    let some ci := env.find? c | throwError "unknown constant {c}"
    return ci.instantiateTypeLevelParams us
  let levels ← types.mapM getLevel
  let v ← getLevel type
  let k := occs.size
  withLocalDeclsDND (occs.mapIdx fun i _ => ((`x).appendIndexAfter i, types[i]!)) fun xs => do
    -- the motive; abstracting free variables gets the de Bruijn indices right under binders
    let M ← mkLambdaFVars xs <| e.replace fun
      | .const c us => (occs.findIdx? (· == (c, us))).map (xs[·]!)
      | _ => none
    let origs := occs.map fun (c, us) => mkConst c us
    let copies := occs.map fun (c, us) => mkConst (eqs.find? c).get!.1 us
    let mut args := origs
    let mut proof? : Option Expr := none
    let mut lhs := e
    for i in [0:k] do
      let (c, us) := occs[i]!
      let h := mkConst (eqs.find? c).get!.2 us
      let f ← withLocalDeclD `y types[i]! fun y =>
        mkLambdaFVars #[y] (mkAppN M (args.set! i y)).headBeta
      let step := mkApp6 (mkConst ``congrArg [levels[i]!, v]) types[i]! type origs[i]! copies[i]! f h
      args := args.set! i copies[i]!
      let rhs := (mkAppN M args).headBeta
      proof? := some <| match proof? with
        | none => step
        | some p => mkApp6 (mkConst ``Eq.trans [v]) type e lhs rhs p step
      lhs := rhs
    return proof?

/-- `@a.{us} = @b.{us}` for constants `a`, `b` of the same type. -/
def mkConstEq (a b : Name) (lvls : List Name) (type : Expr) : MetaM Expr := do
  let us := lvls.map mkLevelParam
  let u ← getLevel type
  return mkApp3 (mkConst ``Eq [u]) type (mkConst a us) (mkConst b us)

/-- Create (or find) the kernel-reducible copy of definition `c`, together with the theorem
`@c = @copy` (checked by the kernel by `rfl`). Returns `none` if the kernel does not accept the
copy; `c` is then used as it is. -/
partial def copyConst (c : Name) : CopyM (Option Name) := do
  if let some c' := (← get).subst.find? c then return some c'
  if (← get).failed.contains c then return none
  let env ← getEnv
  let some (.defnInfo d) := env.find? c
    | throwError "NativeTrust: cannot copy `{c}`: not a definition"
  let cfg ← read
  let name := (← copyPrefix cfg.wfAcc) ++ c
  let eqName := name ++ `_eq
  let body ← if cfg.opt then inlineSimp env cfg d.value else pure d.value
  for dep in body.getUsedConstants do
    if dep != c && (← needsCopy dep) then discard <| copyConst dep
  -- an earlier call in this module may already have made it
  if !env.contains name then
    let value := substConsts (← get).subst body
    let envBefore ← getEnv
    try
      if cfg.trace then eprintRaw s!"NT copying {c}"
      let t0 ← IO.monoMsNow
      addDeclSync <| .defnDecl { d with name, value, all := [name] }
      let t1 ← IO.monoMsNow
      let eqType ← mkConstEq c name d.levelParams d.type
      let us := d.levelParams.map mkLevelParam
      let u ← getLevel d.type
      let refl := mkApp2 (mkConst ``Eq.refl [u]) d.type (mkConst c us)
      -- `c = body` by `rfl` (only inlining differs: no recursive call is compared with a copy),
      -- then `body = value` by congruence from the equations of the copied dependencies
      let st ← get
      let depEqs : NameMap (Name × Name) := st.subst.foldl (fun m o r =>
        match st.eqs.find? o with | some h => m.insert o (r, h) | none => m) {}
      let viaCongr ← match ← congrSubst body d.type depEqs with
        | some h => pure <| some (mkApp6 (mkConst ``Eq.trans [u]) d.type (mkConst c us) body value refl h)
        | none => pure none
      let mkEq (v : Expr) : Declaration :=
        .thmDecl { name := eqName, levelParams := d.levelParams, type := eqType, value := v }
      let ok ← match viaCongr with
        | some pf =>
          let envB ← getEnv
          try
            withOptions (fun o => maxHeartbeats.set o cfg.rflHeartbeats) (addDeclSync (mkEq pf))
            pure true
          catch ex =>
            setEnv envB
            modify fun s => { s with lastCongrError := some m!"{c}: {ex.toMessageData}" }
            pure false
        | none => pure false
      -- fallback `rfl`: the kernel compares `c` with its copy by unfolding, which can amount to
      -- evaluating both; bounded, and if it does not finish the original is kept (an evaluation
      -- that reaches it may then get stuck, which is reported, instead of hanging here)
      unless ok do
        if cfg.trace then eprintRaw s!"NT copy-rfl {c}"
        withOptions (fun o => maxHeartbeats.set o cfg.rflHeartbeats) (addDeclSync (mkEq refl))
      let t2 ← IO.monoMsNow
      modify fun s => { s with timings := s.timings.push (c, t1 - t0, t2 - t1, ok) }
      if cfg.trace then eprintRaw s!"NT copy {c} defn_ms={t1 - t0} eq_ms={t2 - t1} congr={ok}"
    catch _ =>
      setEnv envBefore
      modify fun s => { s with failed := s.failed.insert c }
      return none
    if (← canRegister) && !cfg.wfAcc then
      let entry : CopyEntry := { orig := c, copy := name, eq := eqName }
      modifyEnv (copyExt.addEntry · entry)
    modify fun s => { s with created := s.created.push name }
  modify fun s => { s with subst := s.subst.insert c name, eqs := s.eqs.insert c eqName }
  return some name

/-- Result of `kernelCopy`. -/
structure CopyResult where
  /-- The expression with constants replaced by their copies (definitionally equal to the input). -/
  expr : Expr
  /-- Copies created. -/
  created : Array Name
  /-- For each replaced constant occurring in the input: the original, its copy and `@orig = @copy`. -/
  replaced : Array (Name × Name × Name)
  /-- Kernel time (ms) to check each new copy and its equation; equation by congruence? -/
  timings : Array (Name × Nat × Nat × Bool) := #[]
  lastCongrError : Option MessageData := none

/-- Replace every constant in `e` that needs a kernel-reducible copy by its copy. -/
def kernelCopy (e : Expr) (cfg : CopyConfig := {}) : MetaM CopyResult := do
  let go : CopyM CopyResult := do
    for c in e.getUsedConstants do
      if (← needsCopy c) then discard <| copyConst c
    let s ← get
    let mut replaced := #[]
    for c in e.getUsedConstants do
      if let some c' := s.subst.find? c then
        replaced := replaced.push (c, c', (s.eqs.find? c).getD .anonymous)
    return { expr := substConsts s.subst e, created := s.created, replaced, timings := s.timings,
             lastCongrError := s.lastCongrError }
  (go.run cfg).run' (CopyState.init (← getEnv) cfg.wf cfg.wfAcc)

end NativeTrust
