import Lean
import NativeTrust.Copy

/-!
# Parametric copies: definitions that occur in types

The copies of `NativeTrust.Copy` keep the original types and are bridged to the originals by congruence
along `@c = @c'`. That fails when a definition that must be copied (it reaches `WellFounded.fix`) also
occurs in types: an instance whose fields reach `WellFounded.fix` and that is a parameter of an inductive
type (`@Ev inst`) or of a class field type (`fmt : Fmt Nat inst`), or that a dependent class field mentions
(`HasExecTrace extends HasExecBytes`). The copy of such a constant is not definitionally equal to it, so
every type that mentions it changes, and the copies of the definitions around it no longer fit their
original types.

Here the replacement is made parametric. The *roots* are the replaced constants at the universe levels
where they occur: `WellFounded.fix.{u, v}` (replacement `fixFuel`, equation `fix_eq_fixFuel`) and the
constants registered with `@[kernel_replace]`. Every definition `c` whose value or type mentions a root or
such a definition gets a generic version
  `c.gen : ∀ (F₁ : T₁) (h₁ : r₁ = F₁) …, T_c[r ↦ F, d ↦ d.gen F h]`
in which the roots are variables: types and values are rewritten together, so the generic definitions are
consistent with each other whatever the roots are. A closed proof is kept and cast (`Eq.mp`) along the
equations `hᵢ` to the rewrite of its type (dependent congruence `congr_dep`, as in `transportCopy`); an
open proof is rewritten like any term (it can mention local variables whose types are rewritten), with the
theorems it uses cast the same way. Roots that `rootsOf` misses (it has a cycle guard) are added when a
body needs them, and the body is rewritten again.

The decided term `e` becomes `E F h := e[…]`, and the kernel proves
  `e = E r rfl` (unfolding: at the original roots every generic definition unfolds to the original),
  `E r rfl = E r' hᵣ` (dependent congruence, one root at a time), and evaluates `E r' hᵣ` to `true`.
Inductive types are not copied; where one of their constructor or field types mentions a rewritten
definition (`class HasFmt where fmt : Fmt Nat instSizer`), values are re-wrapped field by field
(`coerce`), which is the identity up to structure eta at the original roots.
-/

open Lean Meta

namespace NativeTrust.Param

/-- A root: a replaced constant at universe levels (normalized), with its replacement and equation. -/
abbrev RootKey := Name × List Level

structure GenEntry where
  gen : Name
  /-- The root instances that `gen` abstracts, in binder order, as levels over the definition's level
  parameters. -/
  roots : Array RootKey
  deriving Inhabited

structure PState where
  needs : Std.HashMap Name Bool := {}
  gens : Std.HashMap Name (Option GenEntry) := {}
  rootsMemo : Std.HashMap Name (Array RootKey) := {}
  inProgress : NameSet := {}
  created : Array Name := #[]
  errors : Array MessageData := #[]
  /-- Root instances that a generic body needed but its root set (`rootsOf`) lacked: `rootsOf` is
  computed with a cycle guard (definitions can mention each other through their types), so it can
  miss roots; the body is then rewritten again with the missing roots added. -/
  missing : Array RootKey := #[]

/-- The replaced constants: `orig ↦ (replacement, theorem @orig = @replacement)`. -/
abbrev Reps := NameMap (Name × Name)

abbrev PM := ReaderT (CopyConfig × Reps) (StateRefT PState MetaM)

def cfgM : PM CopyConfig := return (← read).1
def repsM : PM Reps := return (← read).2

def normLevels (us : List Level) : List Level := us.map Level.normalize

/-- Constants that are never generalized: NativeTrust's own replacements (their bodies mention
`WellFounded.fix` on purpose) and constants that cannot be evaluated anyway. -/
def excluded (reps : Reps) (c : Name) : Bool :=
  reps.contains c || (reps.toList.any fun (_, (r, _)) => r == c) ||
  c == ``NativeTrust.fixFuel || c == ``NativeTrust.fixFuelAux || c == ``NativeTrust.wfFix ||
  c == ``NativeTrust.accGen || kernelPrimitives.contains c || uncopyable.contains c

/-- Does `c` need a generic version: is it a definition whose value or type mentions a root or a
definition that needs one? -/
partial def needsGen (c : Name) : PM Bool := do
  let reps ← repsM
  if excluded reps c then return false
  if let some b := (← get).needs[c]? then return b
  modify fun s => { s with needs := s.needs.insert c false }
  let r ← match (← getEnv).find? c with
    | some (.defnInfo d) =>
      if d.safety != .safe then pure false
      else (d.value.getUsedConstants ++ d.type.getUsedConstants).anyM fun d' =>
        return reps.contains d' || (← needsGen d')
    | _ => pure false
  modify fun s => { s with needs := s.needs.insert c r }
  return r

def addRoot (out : Array RootKey) (k : RootKey) : Array RootKey :=
  if out.any (· == k) then out else out.push k

/-- Root instances used in `e` directly or through definitions that need generic versions (`rootsOf`),
as levels in `e`'s own level parameters. -/
partial def rootsOfExpr (e : Expr) : PM (Array RootKey) := do
  let reps ← repsM
  let env ← getEnv
  let mut out : Array RootKey := #[]
  for (n, us) in (collectOccs reps e).toArray do
    out := addRoot out (n, normLevels us)
  let names := e.getUsedConstants
  let mut deps : NameMap Unit := {}
  for n in names do
    if (← needsGen n) then deps := deps.insert n ()
  for (n, us) in (collectOccs deps e).toArray do
    let some ci := env.find? n | continue
    for (rn, rls) in (← rootsOf n) do
      out := addRoot out (rn, normLevels (rls.map (·.instantiateParams ci.levelParams us)))
  return out
where
  rootsOf (c : Name) : PM (Array RootKey) := do
    if let some r := (← get).rootsMemo[c]? then return r
    if (← get).inProgress.contains c then return #[]
    modify fun s => { s with inProgress := s.inProgress.insert c }
    let some (.defnInfo d) := (← getEnv).find? c | return #[]
    let r1 ← rootsOfExpr d.type
    let r2 ← rootsOfExpr d.value
    let r := r2.foldl addRoot r1
    modify fun s => { s with rootsMemo := s.rootsMemo.insert c r, inProgress := s.inProgress.erase c }
    return r

def rootsOf (c : Name) : PM (Array RootKey) := rootsOfExpr.rootsOf c

/-- The context of a generic body: the root instances with their free variables `F` and `h`. -/
structure GenCtx where
  roots : Array RootKey
  fs : Array Expr
  hs : Array Expr
  /-- `rᵢ` as constants, `Eq.refl rᵢ`, the types and levels of the roots -/
  origs : Array Expr
  rfls : Array Expr
  types : Array Expr
  levels : Array Level

def GenCtx.find? (ctx : GenCtx) (k : RootKey) : Option Nat :=
  ctx.roots.findIdx? (· == k)

/-- `T = T'` for a proposition `T` and its rewrite `T'` (which mentions the `F`/`h` variables): at
`F := r, h := rfl` the rewrite unfolds to `T`, and dependent congruence along each `hᵢ` turns it into
`T'` (as `castProof` in `transportCopy`). -/
def castAlong (ctx : GenCtx) (T T' : Expr) : MetaM Expr := do
  let n := ctx.roots.size
  let vars := ctx.fs ++ ctx.hs
  let mut proof := mkApp2 (mkConst ``Eq.refl [1]) (mkSort levelZero) T
  let mut curF := ctx.origs
  let mut curH := ctx.rfls
  let mut lhs := T
  for i in [0:n] do
    unless T'.containsFVar ctx.fs[i]!.fvarId! || T'.containsFVar ctx.hs[i]!.fvarId! do
      curF := curF.set! i ctx.fs[i]!; curH := curH.set! i ctx.hs[i]!
      continue
    let (cf, ch) := (curF, curH)
    let eqTo (t : Expr) := mkApp3 (mkConst ``Eq [ctx.levels[i]!]) ctx.types[i]! ctx.origs[i]! t
    let Fi ← withLocalDeclD `y ctx.types[i]! fun y =>
      withLocalDeclD `hy (eqTo y) fun hy =>
        mkLambdaFVars #[y, hy] (T'.replaceFVars vars (cf.set! i y ++ ch.set! i hy))
    let step := mkAppN (mkConst ``NativeTrust.congr_dep [ctx.levels[i]!, 1])
      #[ctx.types[i]!, mkSort levelZero, ctx.origs[i]!, Fi, ctx.fs[i]!, ctx.hs[i]!]
    curF := curF.set! i ctx.fs[i]!
    curH := curH.set! i ctx.hs[i]!
    let rhs := T'.replaceFVars vars (curF ++ curH)
    proof := mkApp6 (mkConst ``Eq.trans [1]) (mkSort levelZero) T lhs rhs proof step
    lhs := rhs
  return proof

/-- The root arguments `F₁ h₁ F₂ h₂ …` for a use of `n.{us}` whose generic version abstracts `roots`
(levels over `n`'s parameters `ps`). -/
def rootArgs (ctx : GenCtx) (ps : List Name) (us : List Level) (roots : Array RootKey) :
    PM (Array Expr) := do
  let mut out := #[]
  for (rn, rls) in roots do
    let k := (rn, normLevels (rls.map (·.instantiateParams ps us)))
    let some i := ctx.find? k
      | modify (fun s => { s with missing := addRoot s.missing k })
        throwError "NativeTrust: parametric copy: root {rn}.{k.2} is not abstracted here"
    out := (out.push ctx.fs[i]!).push ctx.hs[i]!
  return out

/-- Does this constructor's declaration mention a root or a definition with a generic version? Its field
types then fix the original definitions (a rigid boundary: inductive types are not copied). -/
def ctorMentionsGen (ctor : Name) : PM Bool := do
  let some ci := (← getEnv).find? ctor | return false
  let reps ← repsM
  ci.type.getUsedConstants.anyM fun c => return reps.contains c || (← needsGen c)

/-- Is `a` a closed term whose type is a rigid structure (a structure whose constructor type mentions a
rewritten definition)? Such values cannot be rewritten field by field when a field type is a rewritten
inductive (`@ACMEEvent inst`): where possible they are inlined instead (`genExpr`, rules for projections
and applications). -/
def rigidClosed? (a : Expr) : PM (Option Name) := do
  if a.hasFVar || a.hasLooseBVars || a.hasMVar then return none
  unless a.getAppFn.isConst do return none
  let some (.defnInfo _) := (← getEnv).find? a.getAppFn.constName! | return none
  let T ← whnf (← inferType a)
  let .const S _ := T.getAppFn | return none
  let env ← getEnv
  unless isStructure env S do return none
  let some (.inductInfo iv) := env.find? S | return none
  let [ctor] := iv.ctors | return none
  if ← ctorMentionsGen ctor then return some S else return none

/-- `isDefEq` with a heartbeat budget (thousands); `false` when the budget runs out. -/
def isDefEqBounded (a b : Expr) (budget : Nat := 200) : MetaM Bool := do
  let hb ← IO.getNumHeartbeats
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with initHeartbeats := hb, maxHeartbeats := budget * 1000 })
      (isDefEq a b))
    (fun _ => pure false)

/-- Coerce `v : src` to `dst`, two types that differ only in original vs. generic definitions: structures
field by field (the identity up to structure eta at the original roots; this covers parameters that the
fields do not use, such as the instance of `ExtensibleMessageFormat Bytes inst a`), propositions with one
original side by a cast along the root equations (`castAlong`), functions pointwise. `origToGen`: `src`
is the original side. -/
partial def coerce (ctx : GenCtx) (v src dst : Expr) (origToGen : Bool) (depth : Nat := 0) : MetaM Expr := do
  if src == dst then return v
  if depth > 24 then throwError "NativeTrust: parametric copy: coercion too deep"
  if ← isDefEqBounded src dst then return v
  let srcW ← whnf src
  let dstW ← whnf dst
  if srcW.isForall && dstW.isForall then
    let .forallE n dA dB bi := dstW | throwError "unreachable"
    let .forallE _ sA sB _ := srcW | throwError "unreachable"
    return ← withLocalDecl n bi dA fun x => do
      let x' ← coerce ctx x dA sA (!origToGen) (depth + 1)
      let body ← coerce ctx (mkApp v x') (sB.instantiate1 x') (dB.instantiate1 x) origToGen (depth + 1)
      mkLambdaFVars #[x] body
  let env ← getEnv
  match srcW.getAppFn, dstW.getAppFn with
  | .const S1 _, .const S2 us2 =>
    if S1 == S2 && isStructure env S1 then
      let some (.inductInfo iv) := env.find? S1 | throwError "not an inductive"
      let [ctor] := iv.ctors | throwError "not a structure"
      let some (.ctorInfo cv) := env.find? ctor | throwError "not a constructor"
      let params := dstW.getAppArgs.extract 0 cv.numParams
      let mut ctorT ← instantiateForall (cv.type.instantiateLevelParams cv.levelParams us2) params
      let mut fields := #[]
      for j in [0:cv.numFields] do
        ctorT ← whnf ctorT
        let .forallE _ fT b _ := ctorT | throwError "constructor type"
        let pj := Expr.proj S1 j v
        let pjT ← inferType pj
        let fj ← coerce ctx pj pjT fT origToGen (depth + 1)
        fields := fields.push fj
        ctorT := b.instantiate1 fj
      return mkAppN (mkConst ctor us2) (params ++ fields)
    else if ← isProp src then
      let (o, g) := if origToGen then (src, dst) else (dst, src)
      let H ← castAlong ctx o g
      let H := if origToGen then H else mkApp4 (mkConst ``Eq.symm [1]) (mkSort levelZero) o g H
      return mkApp4 (mkConst ``Eq.mp [levelZero]) src dst H v
    else throwError "NativeTrust: parametric copy: cannot coerce{indentExpr src}\nto{indentExpr dst}"
  | _, _ =>
    if ← isProp src then
      let (o, g) := if origToGen then (src, dst) else (dst, src)
      let H ← castAlong ctx o g
      let H := if origToGen then H else mkApp4 (mkConst ``Eq.symm [1]) (mkSort levelZero) o g H
      return mkApp4 (mkConst ``Eq.mp [levelZero]) src dst H v
    throwError "NativeTrust: parametric copy: cannot coerce{indentExpr src}\nto{indentExpr dst}"

/-- Run `k` with the root variables `F₀ h₀ F₁ h₁ …` in the local context. -/
partial def withRootVars {α} (roots : Array RootKey) (types : Array Expr) (levels : Array Level)
    (k : Array Expr → Array Expr → PM α) (i : Nat := 0) (fs hs : Array Expr := #[]) : PM α := do
  if h : i < roots.size then
    let (rn, rls) := roots[i]
    withLocalDeclD ((`F).appendIndexAfter i) types[i]! fun f =>
      withLocalDeclD ((`h).appendIndexAfter i)
          (mkApp3 (mkConst ``Eq [levels[i]!]) types[i]! (mkConst rn rls) f) fun hv =>
        withRootVars roots types levels k (i + 1) (fs.push f) (hs.push hv)
  else k fs hs

mutual

/-- The generic rewrite of `e` in `ctx`: roots become their variables, definitions that need generic
versions become `d.gen F h`, closed proofs and theorems whose types change are cast along the equations,
and values crossing a rigid inductive (its constructor types mention rewritten definitions) are coerced. -/
partial def genExpr (ctx : GenCtx) (fuel : Nat) (e : Expr) : PM Expr := do
  let reps ← repsM
  Meta.transform e
    (pre := fun e => do
      if e.isFVar || e.isSort || e.isBVar then return .continue
      let isPf ← try isProof e catch _ => pure false
      unless isPf do
        -- a projection of a closed value of a rigid structure: the field, from the value's constructor
        if let .proj S i a := e then
          if (← rigidClosed? a).isSome then
            let a' ← whnf a
            if let .const cn _ := a'.getAppFn then
              if let some (.ctorInfo cv) := (← getEnv).find? cn then
                if cv.induct == S && a'.getAppNumArgs == cv.numParams + cv.numFields then
                  return .visit (a'.getArg! (cv.numParams + i))
        -- a definition applied to a closed value of a rigid structure: unfolded, so that its projections
        -- of that value are inlined (no rigid value has to be rebuilt over rewritten types)
        if let .const fn us := e.getAppFn then
          if e.isApp && !reps.contains fn then
            if let some (.defnInfo fv) := (← getEnv).find? fn then
              if fv.safety == .safe && (← e.getAppArgs.anyM fun a => return (← rigidClosed? a).isSome) then
                return .visit ((fv.value.instantiateLevelParams fv.levelParams us).beta e.getAppArgs)
        return .continue
      -- an open proof can mention local variables whose types are rewritten: rewrite it as well (theorem
      -- constants are cast in `post`)
      if e.hasFVar then return .continue
      -- a closed proof: kept, and cast to the rewrite of its type
      let T ← inferType e
      let mentions ← T.getUsedConstants.anyM fun c => return reps.contains c || (← needsGen c)
      unless mentions do return .done e
      if fuel == 0 then throwError "NativeTrust: parametric copy: proofs nested too deeply in types"
      let T' ← genExpr ctx (fuel - 1) T
      if T' == T then return .done e
      return .done (mkApp4 (mkConst ``Eq.mp [levelZero]) T T' (← castAlong ctx T T') e))
    (post := fun e => do
      match e with
      | .const n us =>
        -- a theorem (inside a rewritten proof) whose statement mentions rewritten definitions: cast it
        if let some (.thmInfo tv) := (← getEnv).find? n then
          let T := tv.type.instantiateLevelParams tv.levelParams us
          let mentions ← T.getUsedConstants.anyM fun c => return reps.contains c || (← needsGen c)
          unless mentions do return .done e
          if fuel == 0 then throwError "NativeTrust: parametric copy: proofs nested too deeply in types"
          let T' ← genExpr ctx (fuel - 1) T
          if T' == T then return .done e
          return .done (mkApp4 (mkConst ``Eq.mp [levelZero]) T T' (← castAlong ctx T T') e)
        if reps.contains n then
          let some i := ctx.find? (n, normLevels us)
            | modify (fun s => { s with missing := addRoot s.missing (n, normLevels us) })
              throwError "NativeTrust: parametric copy: root {n}.{us} is not abstracted here"
          return .done ctx.fs[i]!
        if !(← needsGen n) then return .done e
        let some g ← genConst n
          | throwError "NativeTrust: parametric copy: no generic version of {n}"
        let ps := ((← getEnv).find? n).get!.levelParams
        return .done (mkAppN (mkConst g.gen us) (← rootArgs ctx ps us g.roots))
      | .proj S _ _ =>
        -- a field of a rigid structure: its declared type mentions original definitions
        let some (.inductInfo iv) := (← getEnv).find? S | return .done e
        let [ctor] := iv.ctors | return .done e
        unless ← ctorMentionsGen ctor do return .done e
        let T ← inferType e
        let T' ← genExpr ctx fuel T
        if T' == T then return .done e
        return .done (← coerce ctx e T T' true)
      | .app .. =>
        let f := e.getAppFn
        let .const cn us := f | return .done e
        let some (.ctorInfo cv) := (← getEnv).find? cn | return .done e
        let args := e.getAppArgs
        unless args.size == cv.numParams + cv.numFields do return .done e
        unless ← ctorMentionsGen cn do return .done e
        -- a constructor of a rigid inductive: fields from their generic types to the declared ones
        let params := args.extract 0 cv.numParams
        let mut ctorT ← instantiateForall (cv.type.instantiateLevelParams cv.levelParams us) params
        let mut newArgs := params
        for j in [0:cv.numFields] do
          ctorT ← whnf ctorT
          let .forallE _ fT b _ := ctorT | return .done e
          let a := args[cv.numParams + j]!
          let aT ← inferType a
          let a' ← coerce ctx a aT fT false
          newArgs := newArgs.push a'
          ctorT := b.instantiate1 a'
        return .done (mkAppN f newArgs)
      | _ => return .done e)

/-- The generic version of definition `c` (made on first use), or `none` if the kernel rejected it. -/
partial def genConst (c : Name) : PM (Option GenEntry) := do
  if let some r := (← get).gens[c]? then return r
  modify fun s => { s with gens := s.gens.insert c none }
  let some (.defnInfo d) := (← getEnv).find? c | return none
  let saved := (← get).missing
  let env ← getEnv
  let pfx := match env.asyncPrefix? with
    | some p => p ++ `_ktp
    | none => `_ktp ++ env.mainModule
  let base := pfx ++ c
  -- generic versions are made per decided term: a second term in the same module gets fresh names
  let mut name := base
  let mut k := 1
  while env.contains name do
    name := base.appendIndexAfter k
    k := k + 1
  let cfg ← cfgM
  let mut roots ← rootsOf c
  let mut result : Option GenEntry := none
  for attempt in [0:6] do
    modify fun s => { s with missing := #[] }
    let rootTypes ← roots.mapM fun (rn, rls) => do
      let some ci := env.find? rn | throwError "unknown constant {rn}"
      return ci.instantiateTypeLevelParams rls
    let levels ← rootTypes.mapM fun t => (getLevel t : MetaM Level)
    let origs := roots.map fun (rn, rls) => mkConst rn rls
    let rfls := roots.mapIdx fun i _ => mkApp2 (mkConst ``Eq.refl [levels[i]!]) rootTypes[i]! origs[i]!
    let rs := roots
    try
      let (value, type) ← withRootVars rs rootTypes levels fun fs hs => do
        let ctx : GenCtx := { roots := rs, fs, hs, origs, rfls, types := rootTypes, levels }
        let T' ← genExpr ctx 8 d.type
        let B' ← genExpr ctx 8 d.value
        let vars := (Array.range rs.size).foldl (fun acc i => (acc.push fs[i]!).push hs[i]!) #[]
        return (← mkLambdaFVars vars B', ← mkForallFVars vars T')
      let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
      let t0 ← IO.monoMsNow
      addDeclSync <| .defnDecl { name, levelParams := d.levelParams, type, value, hints,
                                 safety := .safe, all := [name] }
      if cfg.trace then eprintRaw s!"NT param-gen {c} roots={rs.size} ms={(← IO.monoMsNow) - t0}"
      let entry : GenEntry := { gen := name, roots := rs }
      modify fun s => { s with gens := s.gens.insert c (some entry), created := s.created.push name,
                               rootsMemo := s.rootsMemo.insert c rs }
      result := some entry
      break
    catch ex =>
      let miss := (← get).missing
      if !miss.isEmpty && attempt < 5 then
        -- roots that `rootsOf` missed (a cycle through types): add them and rewrite again
        if cfg.trace then eprintRaw s!"NT param-gen-roots {c} added={miss.toList.map (fun (n, ls) => s!"{n}.{ls}")}"
        roots := miss.foldl addRoot roots
        modify fun s => { s with rootsMemo := s.rootsMemo.insert c roots }
        continue
      if cfg.trace then
        let m := (← ex.toMessageData.toString).replace "\n" " "
        eprintRaw s!"NT param-gen-failed {c}: {m.take 700}"
      modify fun s => { s with errors := s.errors.push m!"{c}: {ex.toMessageData}" }
      break
  modify fun s => { s with missing := saved }
  return result

end

/-- The generic rewrite of a closed term: `E := fun F₁ h₁ … => e[…]` over the roots used by `e`, with the
roots, their replacements and equations, types and levels, and the generic definitions created. -/
structure ParamTerm where
  E : Expr
  origs : Array Expr
  rfls : Array Expr
  repls : Array Expr
  eqs : Array Expr
  types : Array Expr
  levels : Array Level
  created : Array Name
  errors : Array MessageData

def paramTerm (e : Expr) (cfg : CopyConfig) : MetaM ParamTerm := do
  let env ← getEnv
  let mut reps : Reps := {}
  if cfg.wf then reps := reps.insert ``WellFounded.fix (``NativeTrust.fixFuel, ``NativeTrust.fix_eq_fixFuel)
  for (f, g, thm) in (kernelReplaceExt.getState env).toList do
    reps := reps.insert f (g, thm)
  let go : PM ParamTerm := do
    let mut roots ← rootsOfExpr e
    for attempt in [0:6] do
      modify fun s => { s with missing := #[] }
      let rootTypes ← roots.mapM fun (rn, rls) => do
        let some ci := (← getEnv).find? rn | throwError "unknown constant {rn}"
        return ci.instantiateTypeLevelParams rls
      let levels ← rootTypes.mapM fun t => (getLevel t : MetaM Level)
      let origs := roots.map fun (rn, rls) => mkConst rn rls
      let rfls := roots.mapIdx fun i _ => mkApp2 (mkConst ``Eq.refl [levels[i]!]) rootTypes[i]! origs[i]!
      let repls := roots.map fun (rn, rls) => mkConst (reps.find? rn).get!.1 rls
      let eqs := roots.map fun (rn, rls) => mkConst (reps.find? rn).get!.2 rls
      let rs := roots
      try
        let E ← withRootVars rs rootTypes levels fun fs hs => do
          let ctx : GenCtx := { roots := rs, fs, hs, origs, rfls, types := rootTypes, levels }
          let e' ← genExpr ctx 8 e
          let vars := (Array.range rs.size).foldl (fun acc i => (acc.push fs[i]!).push hs[i]!) #[]
          mkLambdaFVars vars e'
        let st ← get
        return { E, origs, rfls, repls, eqs, types := rootTypes, levels, created := st.created,
                 errors := st.errors }
      catch ex =>
        let miss := (← get).missing
        if !miss.isEmpty && attempt < 5 then
          roots := miss.foldl addRoot roots
          continue
        throw ex
    throwError "NativeTrust: parametric route: the roots did not stabilize"
  (go.run (cfg, reps)).run' {}

end NativeTrust.Param
