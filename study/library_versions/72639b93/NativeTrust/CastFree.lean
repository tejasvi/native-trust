import Lean
import NativeTrust.Copy

/-!
# Cast-free versions of stuck `Decidable` and `Fintype` definitions

The kernel reduces a cast `h ▸ x` (`Eq.rec`, `Eq.mpr`, `cast`) only when the two sides of `h` are
definitionally equal on the arguments at hand. Along an equality proved with `propext` or `Quot.sound`
they usually are not: instances built with `simp`/`rw`, and derived `DecidableEq` instances of
structures with quotient fields (`Nat.Partition`), get stuck in the kernel, while compiled code erases
the cast. When `findStuck` reports such a cast, `castRetryReps` looks at the definition it names and
at the definitions in its body whose values are `Decidable p` or `Fintype α`, and `castFreeVersion?`
builds a version `c'` of each, of the same type and without the cast, by the first rule that applies:

1. unfold and split (`Decidable p`): unfold `p`, decide `∧`/`∨`/`¬` part by part, split with `casesOn`
   on the discriminants of its `match`es (the motive abstracts the discriminant: no equation, no cast),
   and synthesize an instance for each part;
2. inductive equality (`Decidable (x = y)` for a non-recursive inductive type without indices, e.g. a
   structure): `casesOn` on both sides, then `decidable_of_iff` over the equalities of the fields that are
   not proofs (`C.injEq`), decided by a synthesized instance, and `isFalse` by `noConfusion` for
   different constructors;
3. sets (`Fintype ↑A` obtained from `Fintype ↑B` by a cast along a congruence from `A = B`, as `rw`
   builds it): `Fintype.ofFinset B.toFinset`, with membership transported along the equality (a proof,
   not a cast); used only when Mathlib's `Fintype.ofFinset` is available;
4. rewrite (`Decidable p`): each cast `Eq.mpr (congrArg f e) d` (also `Eq.mp`, `cast`, and at types
   `∀ ys, Decidable q` such as `DecidablePred p`) in the body becomes `decidable_of_iff` along
   `Iff.of_eq (congrArg (fun x => q[x]) e)`.

Synthesized instances must not reach the definition being replaced. `c = c'` is proved by `funext` and
`Subsingleton.elim`. The kernel checks `c'` and the equation, and any term of type `Decidable p` or
`Fintype α` is correct by construction, so nothing here is trusted; at worst a rule fails, or the
retried evaluation gets stuck elsewhere. The pairs are used like registered `@[kernel_replace]`
replacements, for one retry of the evaluation (`proveTrueByKernel`).
-/

open Lean Meta

namespace NativeTrust

/-- Casts that the kernel reduces only along an equality whose two sides are definitionally equal.
For each, the first universe level is the level of the cast value. -/
def castHeads : List Name :=
  [``Eq.mpr, ``Eq.mp, ``cast, ``Eq.rec, ``Eq.ndrec, ``Eq.recOn, ``Eq.casesOn, ``HEq.rec, ``HEq.ndrec]

/-- `e` is a cast of data (a value at a level other than `Prop`), which evaluation must reduce. -/
def isDataCast (e : Expr) : Bool :=
  match e.getAppFn with
  | .const k (u :: _) => castHeads.contains k && !u.isZero
  | _ => false

/-- Does `e` contain a cast of data? -/
def hasDataCast (e : Expr) : Bool := (e.find? isDataCast).isSome

/-- The casts of data in `e`: maximal applications only, each distinct one once. -/
def dataCasts (e : Expr) : Array Expr := Id.run do
  let mut out := #[]
  let mut seen : Std.HashSet Expr := {}
  let mut todo := #[e]
  while h : 0 < todo.size do
    let x := todo.back
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.insert x
    match x with
    | .app .. =>
      if isDataCast x then out := out.push x
      todo := todo.push x.getAppFn
      for a in x.getAppArgs do todo := todo.push a
    | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
    | .letE _ t v b _ => todo := ((todo.push t).push v).push b
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return out

/-- The equality proof of a cast application (`h` in `Eq.mpr h x`, the major premise of `Eq.rec`). -/
def castProof? (e : Expr) : Option Expr :=
  match e.getAppFn with
  | .const k _ =>
    let args := e.getAppArgs
    if k == ``Eq.mpr || k == ``Eq.mp || k == ``cast then args[2]?
    else if k == ``Eq.rec || k == ``Eq.ndrec then args[5]?
    else if k == ``Eq.recOn || k == ``Eq.casesOn then args[4]?
    else if k == ``HEq.rec || k == ``HEq.ndrec then args[6]?
    else none
  | _ => none

/-- Every cast of data in the closed term `e` is along a bound variable (a hypothesis of the term, as
`cases h : e` and `match h : e` introduce: such a cast reduces whenever the hypothesis' two sides
become definitionally equal, e.g. once `e` evaluates to the constructor of the branch). -/
def castsAlongHypotheses (e : Expr) : Bool :=
  (dataCasts e).all fun c => match castProof? c with
    | some p => p.consumeMData.isBVar
    | none => false

/-- The class of the values of a definition of type `∀ xs, C`, when it is a subsingleton handled
here: `Decidable` or `Fintype` (`DecidableEq α` and `DecidablePred p` unfold to `Decidable`). -/
def subsingletonClassOf? (type : Expr) : MetaM (Option Name) := do
  try
    forallTelescopeReducing type fun _ concl => do
      match (← whnfR concl).getAppFn with
      | .const n _ => return if n == ``Decidable || n == `Fintype then some n else none
      | _ => return none
  catch _ => return none

/-- Does evaluating `e` reach the constant `target`, through definition bodies? At most `limit`
definitions are visited; beyond that the answer is `false`. -/
def reachesConst (env : Environment) (e : Expr) (target : Name) (limit : Nat := 4000) : Bool := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo : Array Name := e.getUsedConstants
  let mut n := 0
  while h : 0 < todo.size do
    let c := todo.back
    todo := todo.pop
    if c == target then return true
    if seen.contains c then continue
    seen := seen.insert c
    n := n + 1
    if n > limit then return false
    if let some (.defnInfo d) := env.find? c then
      for dep in d.value.getUsedConstants do
        unless seen.contains dep do todo := todo.push dep
  return false

/-- Run a synthesis step under a heartbeat budget (thousands; `0` = none); `none` when it fails, throws
or runs out (runtime exceptions included): a rule that gives up is simply not used. -/
def castBounded {α : Type} (budget : Nat) (x : MetaM (Option α)) : MetaM (Option α) := do
  let x : MetaM (Option α) := do try x catch _ => pure none
  let x := if budget == 0 then x else do
    let hb ← IO.getNumHeartbeats
    withTheReader Core.Context (fun c => { c with initHeartbeats := hb, maxHeartbeats := budget * 1000 }) x
  tryCatchRuntimeEx x (fun _ => pure none)

/-- An instance of `goal` found by synthesis whose evaluation reaches none of `avoid` (the definitions
being replaced: synthesis would often find them again). -/
def synthAvoiding? (goal : Expr) (avoid : Array Name) : MetaM (Option Expr) := do
  let some inst ← (try synthInstance? goal catch _ => pure none) | return none
  let inst ← instantiateMVars inst
  if inst.hasMVar then return none
  let env ← getEnv
  if avoid.any (reachesConst env inst ·) then return none
  return some inst

/-- `e` with the `match` applications whose discriminants are constructors reduced. -/
def reduceMatchers (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    if (← isMatcherApp x) then
      match ← reduceMatcher? x with
      | .reduced x' => return .visit x'.headBeta
      | _ => return .done x
    return .done x)

/-- The `match` applications in `e` (outermost first). -/
partial def collectMatcherApps (env : Environment) (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  match e with
  | .app .. =>
    let acc := match e.getAppFn with
      | .const c _ => if isMatcherCore env c then acc.push e else acc
      | _ => acc
    e.getAppArgs.foldl (fun a x => collectMatcherApps env x a) acc
  | .lam _ t b _ | .forallE _ t b _ => collectMatcherApps env b (collectMatcherApps env t acc)
  | .letE _ t v b _ => collectMatcherApps env b (collectMatcherApps env v (collectMatcherApps env t acc))
  | .mdata _ b | .proj _ _ b => collectMatcherApps env b acc
  | _ => acc

/-- A discriminant of a `match` in `p` to split on: closed under the binders of `p`, not a
constructor application, of an inductive type without indices. -/
def findSplitDiscr? (p : Expr) : MetaM (Option Expr) := do
  let env ← getEnv
  for m in collectMatcherApps env p do
    let some mapp ← matchMatcherApp? m | continue
    for d in mapp.discrs do
      if d.hasLooseBVars || d.hasMVar then continue
      let dw ← whnfR d
      if let .const k _ := dw.getAppFn then
        if env.find? k matches some (.ctorInfo _) then continue
      let ty ← whnf (← inferType d)
      let .const I _ := ty.getAppFn | continue
      let some (.inductInfo ival) := env.find? I | continue
      if ival.numIndices == 0 && ty.getAppNumArgs == ival.numParams then return some d
  return none

mutual

/-- Rule 1: a `Decidable p` instance without casts: synthesis (avoiding `avoid`), else a `casesOn`
split on a discriminant of a `match` in `p`, else the unfolded `p` (`fuel` bounds the steps). -/
partial def synthDecSplit (p : Expr) (avoid : Array Name) (fuel : Nat) : MetaM (Option Expr) := do
  if let some inst ← synthAvoiding? (mkApp (mkConst ``Decidable) p) avoid then return some inst
  if fuel == 0 then return none
  -- connectives: the parts separately (the term shrinks, so no fuel is spent)
  let pw := p.consumeMData
  if pw.isAppOfArity ``And 2 || pw.isAppOfArity ``Or 2 then
    let a := pw.appFn!.appArg!
    let b := pw.appArg!
    let some ia ← synthDecSplit a avoid fuel | return none
    let some ib ← synthDecSplit b avoid fuel | return none
    let inst := if pw.isAppOfArity ``And 2 then ``instDecidableAnd else ``instDecidableOr
    return some (mkApp4 (mkConst inst) a b ia ib)
  if pw.isAppOfArity ``Not 1 then
    let some ia ← synthDecSplit pw.appArg! avoid fuel | return none
    return some (mkApp2 (mkConst ``instDecidableNot) pw.appArg! ia)
  if let some d ← findSplitDiscr? p then return ← splitDec p d avoid (fuel - 1)
  let p' ← reduceMatchers (← whnfCore p)
  if p' != p then return ← synthDecSplit p' avoid (fuel - 1)
  if let some p' ← unfoldDefinition? p then return ← synthDecSplit p'.headBeta avoid (fuel - 1)
  return none

/-- `I.casesOn (motive := fun x => Decidable p[x/d]) d (fun fields => inst)`, one instance per
constructor. `Decidable p[C fields/d]` is definitionally `Decidable p` reduced, so no cast appears. -/
partial def splitDec (p d : Expr) (avoid : Array Name) (fuel : Nat) : MetaM (Option Expr) := do
  let env ← getEnv
  let dType ← whnf (← inferType d)
  let .const I us := dType.getAppFn | return none
  let some (.inductInfo ival) := env.find? I | return none
  let params := dType.getAppArgs
  unless ival.numIndices == 0 && params.size == ival.numParams do return none
  let pAbs ← kabstract p d
  unless pAbs.hasLooseBVars do return none
  let motive := Expr.lam `x dType (mkApp (mkConst ``Decidable) pAbs) .default
  unless ← isTypeCorrect motive do return none
  let casesOn := mkCasesOnName I
  let some casesInfo := env.find? casesOn | return none
  -- `casesOn` must eliminate into `Type` (its first level is the motive's)
  unless casesInfo.levelParams.length == us.length + 1 do return none
  let mut minors := #[]
  for ctor in ival.ctors do
    let cinfo ← getConstInfoCtor ctor
    let cty ← instantiateForall (cinfo.instantiateTypeLevelParams us) params
    let minor? ← forallTelescopeReducing cty fun fields _ => do
      let ctorApp := mkAppN (mkConst ctor us) (params ++ fields)
      let pc ← reduceMatchers (pAbs.instantiate1 ctorApp)
      let some inst ← synthDecSplit pc avoid fuel | return none
      return some (← mkLambdaFVars fields inst)
    let some minor := minor? | return none
    minors := minors.push minor
  return some (mkAppN (mkConst casesOn (levelOne :: us)) (params ++ #[motive, d] ++ minors))

end

/-- The injectivity theorem `C.injEq` of the constructor `C`, when it exists (not every type has one:
`genInjectivity`). Never made here: a theorem with a global name made in one module would clash with the
same theorem made in another. -/
def injEqOf? (ctor : Name) : MetaM (Option ConstantInfo) :=
  return (← getEnv).find? (ctor ++ `injEq)

/-- For a structure-like type `S` (one constructor) without `injEq`: the conjunction `conj` of the
equalities of the fields that are not proofs, and a proof of `(ca = cb) ↔ conj` for `ca`, `cb` the
constructor applied to the fields `as`, `bs` (free variables): `→` by projections, `←` by `subst` and
proof irrelevance. `none` when a field's type depends on an earlier field. -/
def structFieldsIff? (S : Name) (αw ca cb : Expr) (as bs : Array Expr) : MetaM (Option (Expr × Expr)) := do
  let mut idx := #[]
  for i in [0:as.size] do
    let ta ← inferType as[i]!
    if ← isProp ta then continue
    unless ← isDefEq ta (← inferType bs[i]!) do return none
    idx := idx.push i
  let eqs ← idx.mapM fun i => mkEq as[i]! bs[i]!
  let conj := if eqs.isEmpty then mkConst ``True else
    eqs.pop.foldr (fun e acc => mkApp2 (mkConst ``And) e acc) eqs.back!
  let eqT ← mkEq ca cb
  -- `→`: each field equality is a congruence of the projection; right-nested `And.intro`
  let mp ← withLocalDeclD `h eqT fun h => do
    let parts ← idx.mapM fun i => do
      let f ← withLocalDeclD `z αw fun z => mkLambdaFVars #[z] (.proj S i z)
      mkCongrArg f h
    let mut pf := if parts.isEmpty then mkConst ``True.intro else parts.back!
    let mut ty := if eqs.isEmpty then mkConst ``True else eqs.back!
    for j in (List.range (parts.size - 1)).reverse do
      pf := mkApp4 (mkConst ``And.intro) eqs[j]! ty parts[j]! pf
      ty := mkApp2 (mkConst ``And) eqs[j]! ty
    mkLambdaFVars #[h] pf
  -- `←`: `∀ e₁ … eₖ, ca = cb` by substituting the field equalities, then `rfl` (the proof fields agree
  -- by proof irrelevance)
  let g ← mkFreshExprSyntheticOpaqueMVar (← eqs.foldrM (fun e acc => mkArrow e acc) eqT)
  let names := (List.range eqs.size).map fun i => Name.mkSimple s!"_cfe{i}"
  let (_, m) ← g.mvarId!.introN eqs.size names
  let mut m := m
  for nm in names do
    -- `subst` renames the hypotheses it reverts; find each by its name
    let some decl := (← m.getDecl).lctx.findFromUserName? nm | throwError "lost hypothesis {nm}"
    m ← subst m decl.fvarId
  m.refl
  let allE ← instantiateMVars g
  let mpr ← withLocalDeclD `hc conj fun hc => do
    -- the conjunction's components (right-nested)
    let mut comps := #[]
    let mut cur := hc
    for j in [0:eqs.size] do
      if j + 1 == eqs.size then comps := comps.push cur
      else
        let rest := eqs.extract (j + 1) eqs.size
        let restConj := rest.pop.foldr (fun e acc => mkApp2 (mkConst ``And) e acc) rest.back!
        comps := comps.push (mkApp3 (mkConst ``And.left) eqs[j]! restConj cur)
        cur := mkApp3 (mkConst ``And.right) eqs[j]! restConj cur
    mkLambdaFVars #[hc] (mkAppN allE comps)
  return some (conj, mkApp4 (mkConst ``Iff.intro) eqT conj mp mpr)

/-- Rule 2: `Decidable (x = y)` for an inductive type without indices that is not recursive (a structure,
or a type whose constructors have non-recursive fields): `casesOn` on both sides; for the same
constructor `C`, `decidable_of_iff (a₁ = b₁ ∧ …) (Iff.of_eq (C.injEq …)).symm`, the equalities of the fields
that are not proofs decided by a synthesized instance (avoiding `avoid`), or `isTrue rfl` when `C` has no
fields; for different constructors, `isFalse` by `noConfusion`. -/
def castFreeIndEq? (p : Expr) (avoid : Array Name) (maxCtors : Nat := 16) : MetaM (Option Expr) := do
  let env ← getEnv
  let some (α, x, y) := (← whnfR p).eq? | return none
  let αw ← whnf α
  let .const I us := αw.getAppFn | return none
  let some (.inductInfo ival) := env.find? I | return none
  unless ival.numIndices == 0 && !ival.isRec && !ival.ctors.isEmpty && ival.ctors.length ≤ maxCtors do
    return none
  let params := αw.getAppArgs
  unless params.size == ival.numParams do return none
  let casesOn := mkCasesOnName I
  let some casesInfo := env.find? casesOn | return none
  unless casesInfo.levelParams.length == us.length + 1 do return none
  let decOf (q : Expr) := mkApp (mkConst ``Decidable) q
  let ctorTy (ctor : Name) : MetaM Expr := do
    instantiateForall ((← getConstInfoCtor ctor).instantiateTypeLevelParams us) params
  -- the minor premise for `y` = `cj bs`, when `x` = `ci as` (`ca`)
  let sameOrOther (ci cj : Name) (as : Array Expr) (ca : Expr) : MetaM (Option Expr) := do
    forallTelescopeReducing (← ctorTy cj) fun bs _ => do
      let cb := mkAppN (mkConst cj us) (params ++ bs)
      let eqT ← mkEq ca cb
      if ci == cj then
        if as.isEmpty then
          return some (← mkLambdaFVars bs (mkApp2 (mkConst ``Decidable.isTrue) eqT (← mkEqRefl ca)))
        -- `iff : conj ↔ ca = cb`
        let (conj, iff) ← match ← injEqOf? ci with
          | some injInfo =>
            let h := mkAppN (mkConst (ci ++ `injEq) us) (params ++ as ++ bs)
            let hTy ← instantiateForall (injInfo.instantiateTypeLevelParams us) (params ++ as ++ bs)
            let some (_, _, conj) := hTy.eq? | return none
            pure (conj, mkApp3 (mkConst ``Iff.symm) eqT conj (mkApp3 (mkConst ``Iff.of_eq) eqT conj h))
          | none =>
            unless ival.ctors.length == 1 do return none
            let some (conj, pf) ← structFieldsIff? I αw ca cb as bs | return none
            pure (conj, mkApp3 (mkConst ``Iff.symm) eqT conj pf)
        let some inst ← synthAvoiding? (decOf conj) avoid | return none
        return some (← mkLambdaFVars bs (mkApp4 (mkConst ``decidable_of_iff) eqT conj iff inst))
      else
        let ne ← withLocalDeclD `h eqT fun hv => do mkLambdaFVars #[hv] (← mkNoConfusion (mkConst ``False) hv)
        return some (← mkLambdaFVars bs (mkApp2 (mkConst ``Decidable.isFalse) eqT ne))
  let motiveX ← withLocalDeclD `x αw fun xv => do mkLambdaFVars #[xv] (decOf (← mkEq xv y))
  let mut minorsX := #[]
  for ci in ival.ctors do
    let mx? ← forallTelescopeReducing (← ctorTy ci) fun as _ => do
      let ca := mkAppN (mkConst ci us) (params ++ as)
      let motiveY ← withLocalDeclD `y αw fun yv => do mkLambdaFVars #[yv] (decOf (← mkEq ca yv))
      let mut minorsY := #[]
      for cj in ival.ctors do
        let some my ← sameOrOther ci cj as ca | return none
        minorsY := minorsY.push my
      return some (← mkLambdaFVars as (mkAppN (mkConst casesOn (levelOne :: us)) (params ++ #[motiveY, y] ++ minorsY)))
    let some mx := mx? | return none
    minorsX := minorsX.push mx
  return some (mkAppN (mkConst casesOn (levelOne :: us)) (params ++ #[motiveX, x] ++ minorsX))

/-- Strip metadata, `id` wrappers, `let` and `have` (`letFun`) bindings at the head. -/
partial def peelId (e : Expr) : Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``id 2 then peelId e.appArg!
  else match e with
    | .letE _ _ v b _ => peelId (b.instantiate1 v)
    | _ =>
      if e.isAppOfArity ``letFun 4 then peelId (e.getArg! 3 |>.beta #[e.getArg! 2])
      else e

/-- The proof term behind `h`: when `h` applies a theorem (the abstracted proof `foo._proof_1 xs` of a
definition), the theorem's value applied to the arguments. -/
def unfoldProofHead (h : Expr) : MetaM (Option Expr) := do
  let h := peelId h
  let .const t us := h.getAppFn | return none
  let some (.thmInfo tv) := (← getEnv).find? t | return none
  unless tv.levelParams.length == us.length do return none
  return some (peelId ((tv.value.instantiateLevelParams tv.levelParams us).beta h.getAppArgs))

/-- `(a₁, a₂, f, e)` when `h` (after unfolding abstracted proofs, at most `depth` times) is
`congrArg f e` with `e : a₁ = a₂`. -/
partial def congrArgParts? (h : Expr) (depth : Nat := 3) :
    MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let h := peelId h
  if h.isAppOfArity ``congrArg 6 then
    let args := h.getAppArgs
    return some (args[2]!, args[3]!, args[4]!, args[5]!)
  if depth == 0 then return none
  let some h' ← unfoldProofHead h | return none
  congrArgParts? h' (depth - 1)

/-- `t` with its leading binders (exposed by `whnfR`, so `DecidablePred p` counts) instantiated with
`ys`, then `whnfR`. -/
def instForallR (t : Expr) (ys : Array Expr) : MetaM Expr := do
  let mut t := t
  for y in ys do
    t ← whnfR t
    let .forallE _ _ b _ := t | throwError "not a function type"
    t := b.instantiate1 y
  whnfR t

/-- Rule 4: every cast `Eq.mpr h d` (`Eq.mp h d`, `cast h d`) in `body` between types of the form
`∀ ys, Decidable q` (`Decidable p`, `DecidablePred p`, …) whose proof `h` is `congrArg f e`, as
`simp`/`rw` build it, becomes `fun ys => decidable_of_iff _ (Iff.of_eq (congrArg (fun x => q[x]) e)) (d ys)`
(oriented), where `f x ≡ ∀ ys, Decidable q[x]`. `none` when nothing changes. -/
def castFreeRewrite? (body : Expr) : MetaM (Option Expr) := do
  let changed ← IO.mkRef false
  let r ← Meta.transform body (post := fun e => do
    let .const k _ := e.getAppFn | return .done e
    unless (k == ``Eq.mpr || k == ``Eq.mp || k == ``cast) && e.getAppNumArgs ≥ 4 do return .done e
    let args := e.getAppArgs
    let mpr := k == ``Eq.mpr
    -- `Eq.mpr {α β} (h : α = β) (d : β) : α` and `Eq.mp {α β} (h : α = β) (d : α) : β`
    let (src, tgt) := if mpr then (args[1]!, args[0]!) else (args[0]!, args[1]!)
    let some (a₁, _, f, eq) ← congrArgParts? args[2]! | return .done e
    let r? ← (try forallTelescopeReducing tgt fun ys tgtBody => do
        let tgtBody ← whnfR tgtBody
        unless tgtBody.isAppOfArity ``Decidable 1 do return none
        let srcBody ← instForallR src ys
        unless srcBody.isAppOfArity ``Decidable 1 do return none
        let pT := tgtBody.appArg!
        let pS := srcBody.appArg!
        -- `h : α = β` with `α ≡ f a₁`, `β ≡ f a₂`: the proposition as a function of the argument
        let motive ← withLocalDeclD `x (← inferType a₁) fun x => do
          let fx ← instForallR (f.beta #[x]) ys
          unless fx.isAppOfArity ``Decidable 1 do throwError "not Decidable"
          mkLambdaFVars #[x] fx.appArg!
        let eP ← mkCongrArg motive eq
        -- `Eq.mpr`: `eP : pT = pS`; `Eq.mp`/`cast`: `eP : pS = pT`
        let iff := if mpr then
            mkApp3 (mkConst ``Iff.symm) pT pS (mkApp3 (mkConst ``Iff.of_eq) pT pS eP)
          else mkApp3 (mkConst ``Iff.of_eq) pS pT eP
        let v := mkApp4 (mkConst ``decidable_of_iff) pT pS iff (mkAppN args[3]! ys)
        unless ← isTypeCorrect v do return none
        return some (← mkLambdaFVars ys v)
      catch _ => pure none)
    let some v := r? | return .done e
    changed.set true
    return .done (mkAppN v (args.extract 4 args.size)))
  return if ← changed.get then some r else none

/-- `t` is `Fintype ↑S` (`Fintype (Set.Elem S)`): `S`. -/
def fintypeSetOf? (t : Expr) : Option Expr :=
  let t := t.consumeMData
  if t.isAppOfArity `Fintype 1 then
    let s := t.appArg!.consumeMData
    if s.isAppOfArity `Set.Elem 2 then some s.appArg! else none
  else none

/-- `(S₁, S₂, e : S₁ = S₂)` from a proof `h` of an equality between `Fintype ↑S₁` and `Fintype ↑S₂` (or
between `↑S₁` and `↑S₂`) built by congruence, as `rw` builds it: `congrArg (fun x => Fintype ↑(S x)) e`
gives `congrArg (fun x => S x) e`; `congrArg Fintype e'` looks into `e'`. -/
partial def setEqOf? (h : Expr) (depth : Nat := 2) : MetaM (Option (Expr × Expr × Expr)) := do
  let some (a₁, a₂, f, e) ← congrArgParts? h | return none
  let xTy ← inferType a₁
  let motive? ← withLocalDeclD `x xTy fun x => do
    let fx := (f.beta #[x]).headBeta.consumeMData
    let s := if fx.isAppOfArity `Fintype 1 then fx.appArg!.consumeMData else fx
    if s.isAppOfArity `Set.Elem 2 then return some (← mkLambdaFVars #[x] s.appArg!) else return none
  if let some motive := motive? then
    return some ((motive.beta #[a₁]).headBeta, (motive.beta #[a₂]).headBeta, ← mkCongrArg motive e)
  if depth == 0 then return none
  -- `f x ≡ Fintype x`: the equality of types `e` is itself a congruence
  let isFintypeFn ← withLocalDeclD `x xTy fun x => do
    let fx := (f.beta #[x]).headBeta.consumeMData
    return fx.isAppOfArity `Fintype 1 && fx.appArg!.consumeMData == x
  unless isFintypeFn do return none
  setEqOf? e (depth - 1)

/-- Rule 3: `body` is (up to `id`, `let`, `have`) a cast `Eq.mpr h d` (or `Eq.mp h d`, `cast h d`) from
`d : Fintype ↑B` to `Fintype ↑A`, with `h` a congruence along a set equality (see `setEqOf?`), as
`rw [e]; infer_instance` builds it: `Fintype.ofFinset (@Set.toFinset _ B d) (fun x => Set.mem_toFinset.trans …)`,
membership transported along the equality (a proof). Needs Mathlib (`Fintype.ofFinset`, `Set.toFinset`,
`Set.mem_toFinset`). -/
def castFreeFintypeSet? (concl body : Expr) : MetaM (Option Expr) := do
  let env ← getEnv
  unless [`Fintype.ofFinset, `Set.toFinset, `Set.mem_toFinset, `Set.Elem].all env.contains do return none
  let body := peelId body
  let .const k _ := body.getAppFn | return none
  unless (k == ``Eq.mpr || k == ``Eq.mp || k == ``cast) && body.getAppNumArgs == 4 do return none
  let args := body.getAppArgs
  let srcT := if k == ``Eq.mpr then args[1]! else args[0]!
  let d := args[3]!
  let some a := fintypeSetOf? concl | return none
  let some b := fintypeSetOf? srcT | return none
  let some (l, r, pf) ← setEqOf? args[2]! | return none
  let eAB ← if (← isDefEq l a) && (← isDefEq r b) then pure pf
    else if (← isDefEq l b) && (← isDefEq r a) then mkEqSymm pf
    else return none
  let finsetB ← mkAppOptM `Set.toFinset #[none, some b, some d]
  let ofF ← mkAppOptM `Fintype.ofFinset #[none, some a, some finsetB]
  let hTy ← whnf (← inferType ofF)
  let .forallE _ hDom _ _ := hTy | return none
  let H ← forallTelescopeReducing hDom fun xs _ => do
    let some x := xs[0]? | throwError "no binder"
    let mem ← mkAppOptM `Set.mem_toFinset #[none, some b, some d, some x]
    let memTy ← inferType mem
    let some (_, rhs) := memTy.iff? | throwError "not an iff"
    -- `x ∈ B` with `B` abstracted: the motive of the transport along `eAB.symm : B = A`
    let rAbs ← kabstract rhs b
    unless rAbs.hasLooseBVars do throwError "set not found"
    let motive := Expr.lam `S (← inferType b) rAbs .default
    let step ← mkCongrArg motive (← mkEqSymm eAB)
    let stepIff ← mkAppM ``Iff.of_eq #[step]
    mkLambdaFVars xs (← mkAppM ``Iff.trans #[mem, stepIff])
  return some (mkApp ofF H)

/-- A cast-free value of the definition `c` (same type), and the rule that built it (1-4); see the
module documentation. -/
def synthCastFree? (c : Name) (budget : Nat := 5000) : MetaM (Option (Expr × Nat)) := do
  let some (.defnInfo d) := (← getEnv).find? c | return none
  castBounded budget <| forallTelescopeReducing d.type fun xs concl => do
    let concl ← whnfR concl
    let body := (d.value.beta xs).headBeta
    let finish (v : Expr) (rule : Nat) : MetaM (Option (Expr × Nat)) := do
      let v ← instantiateMVars (← mkLambdaFVars xs v)
      if v.hasMVar || v.hasFVar then return none
      return some (v, rule)
    if concl.isAppOfArity ``Decidable 1 then
      let p := concl.appArg!
      if let some v ← castBounded 0 (synthDecSplit p #[c] 8) then
        if !hasDataCast v then return ← finish v 1
      if let some v ← castBounded 0 (castFreeIndEq? p #[c]) then
        if !hasDataCast v then return ← finish v 2
      if let some v ← castBounded 0 (castFreeRewrite? body) then
        let v' ← instantiateMVars (← mkLambdaFVars xs v)
        if castsAlongHypotheses v' && !reachesConst (← getEnv) v' c then return ← finish v 4
    else if concl.isAppOfArity `Fintype 1 then
      if let some v ← castBounded 0 (castFreeFintypeSet? concl body) then
        if !hasDataCast v then return ← finish v 3
    return none

/-- `@c = @c'` for definitions of the same type whose values are subsingletons, by `funext` over the
arguments and `Subsingleton.elim`. -/
def subsingletonEqProof (c c' : Name) (lvls : List Name) (type : Expr) : MetaM Expr :=
  forallTelescopeReducing type fun xs concl => do
    let u ← getLevel concl
    let inst ← synthInstance (mkApp (mkConst ``Subsingleton [u]) concl)
    let us := lvls.map mkLevelParam
    let mut pf := mkApp4 (mkConst ``Subsingleton.elim [u]) concl inst
      (mkAppN (mkConst c us) xs) (mkAppN (mkConst c' us) xs)
    for i in (List.range xs.size).reverse do
      pf ← mkAppM ``funext #[← mkLambdaFVars #[xs[i]!] pf]
    instantiateMVars pf

/-- Prefix of cast-free versions: `_ktcast.<module>`, or `<decl>._ktcast` inside an asynchronous
proof (like `copyPrefix`). -/
def castFreePrefix : CoreM Name := do
  let env ← getEnv
  match env.asyncPrefix? with
  | some p => return p ++ `_ktcast
  | none => return `_ktcast ++ env.mainModule

/-- Declare `c'` with value `v` (of the type of `c`) and `thm : @c = @c'` (both checked by the kernel).
`false` (environment unchanged) when the kernel rejects either. -/
def castFreeDeclare (c c' : Name) (v : Expr) (rule : Nat) (trace : Bool := false) : MetaM Bool := do
  let some (.defnInfo d) := (← getEnv).find? c | return false
  let envBefore ← getEnv
  try
    addDeclSync <| .defnDecl { d with name := c', value := v, all := [c'] }
    let pf ← subsingletonEqProof c c' d.levelParams d.type
    let eqType ← mkConstEq c c' d.levelParams d.type
    addDeclSync <| .thmDecl { name := c' ++ `_eq, levelParams := d.levelParams, type := eqType, value := pf }
    if trace then eprintRaw s!"NT cast-free {c} rule={rule} as {c'}"
    return true
  catch ex =>
    setEnv envBefore
    if trace then
      let m := (← ex.toMessageData.toString).replace "\n" " "
      eprintRaw s!"NT cast-free {c}: rule {rule} rejected: {m.take 300}"
    return false

/-- Declare the cast-free version `c'` of `c` and `thm : @c = @c'` (both kernel-checked), or find them
when an earlier fact of this module made them. Returns `(c', thm, rule)` (`rule = 0`: found). -/
def castFreeVersion? (c : Name) (budget : Nat := 5000) (trace : Bool := false) :
    MetaM (Option (Name × Name × Nat)) := do
  let c' := (← castFreePrefix) ++ c
  let thm := c' ++ `_eq
  if (← getEnv).contains thm then return some (c', thm, 0)
  let some (v, rule) ← synthCastFree? c budget | do
    if trace then eprintRaw s!"NT cast-free {c}: no rule applies"
    return none
  if ← castFreeDeclare c c' v rule trace then return some (c', thm, rule) else return none

/-- Cast-free versions of several definitions at once (`(c, c', thm)` for those built): the value of
each refers to the cast-free versions of the others (`c'` replaces `c` inside it, e.g. a `Fintype`
built from another stuck one), so the evaluation never meets the originals again. Any value of the
right type is proved equal by `Subsingleton.elim`, so this substitution needs no proof. -/
def castFreeVersions (cs : Array Name) (budget : Nat := 5000) (trace : Bool := false) :
    MetaM (Array (Name × Name × Name)) := do
  let pre ← castFreePrefix
  let mut done : Array (Name × Name × Name) := #[]
  let mut todo : Array (Name × Name × Expr × Nat) := #[]
  for c in cs do
    -- a version made earlier in this module is reused unless its value refers to another of `cs`
    -- (then a fresh one, with a fresh name, refers to that one's cast-free version instead)
    let mut c' := pre ++ c
    let mut k := 0
    let mut reuse := false
    repeat
      let some (.defnInfo d') := (← getEnv).find? c' | break
      unless (← getEnv).contains (c' ++ `_eq) do break
      if d'.value.getUsedConstants.all fun n => n == c || !cs.contains n then reuse := true; break
      k := k + 1
      c' := (pre ++ c).appendIndexAfter k
    if reuse then done := done.push (c, c', c' ++ `_eq); continue
    match ← synthCastFree? c budget with
    | some (v, rule) => todo := todo.push (c, c', v, rule)
    | none => if trace then eprintRaw s!"NT cast-free {c}: no rule applies"
  -- every candidate stands for its cast-free version inside the others' values
  let pairs : Array (Name × Name) :=
    (done.map fun (c, c', _) => (c, c')) ++ (todo.map fun (c, c', _, _) => (c, c'))
  let m : NameMap Name := pairs.foldl (fun m (c, c') => m.insert c c') {}
  -- declare in dependency order (a value may refer to another's `c'`)
  let mut pending := todo.map fun (c, c', v, rule) => (c, c', substConsts (m.erase c) v, rule)
  let mut progress := true
  while progress && !pending.isEmpty do
    progress := false
    let mut rest := #[]
    for (c, c', v, rule) in pending do
      let env ← getEnv
      if v.getUsedConstants.all fun k => env.contains k then
        if ← castFreeDeclare c c' v rule trace then done := done.push (c, c', c' ++ `_eq)
        progress := true
      else rest := rest.push (c, c', v, rule)
    pending := rest
  return done

/-- The original of a kernel-reducible copy made in this module (`_kt….<module>.<original>`). -/
def copyOrigin? (env : Environment) (n : Name) : Option Name :=
  match n.components with
  | (.str .anonymous tag) :: rest =>
    if tag.startsWith "_kt" then
      let modComps := env.mainModule.components
      if rest.take modComps.length == modComps then
        some ((rest.drop modComps.length).foldl (· ++ ·) .anonymous)
      else none
    else none
  | _ => none

/-- The definitions to make cast-free when the evaluation is stuck at a cast below `via`: `via` and
the definitions reachable from its body in at most `depth` steps (at most `visits` definitions) whose
values are `Decidable` or `Fintype` and hold a cast of data (copies stand for their originals; at most
`max`). -/
def castCandidates (via : Name) (depth : Nat := 3) (max : Nat := 4) (visits : Nat := 2000) :
    MetaM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  let mut seen : NameSet := {}
  let mut frontier := #[via]
  let mut n := 0
  for _ in [0:depth + 1] do
    let mut next := #[]
    for c in frontier do
      if seen.contains c then continue
      seen := seen.insert c
      n := n + 1
      if n > visits then return out
      let some (.defnInfo d) := env.find? c | continue
      if d.safety != .safe then continue
      let orig := (copyOrigin? env c).getD c
      unless orig == c || seen.contains orig do next := next.push orig
      if orig == c && hasDataCast d.value && !(`_ktcast).isPrefixOf c then
        if (← subsingletonClassOf? d.type).isSome then
          out := out.push c
          if out.size ≥ max then return out
      for dep in d.value.getUsedConstants do
        unless seen.contains dep do next := next.push dep
    frontier := next
  return out

/-- The definition whose body held the cast `stuck`, when its proof is an abstracted proof of that
definition (`C._proof_3 …`, as Lean names the proofs inside a definition). -/
def castOwner? (stuck : Expr) : Option Name := do
  let p ← castProof? stuck
  let .const n _ := (peelId p).getAppFn | none
  let .str pre s := n | none
  if s.startsWith "_proof_" then some pre else none

/-- When the evaluation is stuck at the cast `stuck` (a `K`-like recursor) below `via`: cast-free
versions of the candidate definitions, as replacements `(c, c', thm)`: the definition owning the cast's
proof (`castOwner?`) and `castCandidates via`, except those in `skip` (already replaced). -/
def castRetryReps (stuck : Expr) (via? : Option Name) (budget : Nat := 5000) (trace : Bool := false)
    (skip : Array Name := #[]) : MetaM (Array (Name × Name × Name)) := do
  let env ← getEnv
  let isK := match stuck.getAppFn with
    | .const k _ => match env.find? k with | some (.recInfo rv) => rv.k | _ => false
    | _ => false
  unless isK do return #[]
  let mut cands : Array Name := #[]
  if let some owner := castOwner? stuck then
    let owner := (copyOrigin? env owner).getD owner
    if let some (.defnInfo d) := env.find? owner then
      if hasDataCast d.value && (← subsingletonClassOf? d.type).isSome then cands := cands.push owner
  if let some via := via? then
    for c in ← castCandidates via do
      unless cands.contains c do cands := cands.push c
  castFreeVersions (cands.filter (!skip.contains ·)) budget trace

end NativeTrust
