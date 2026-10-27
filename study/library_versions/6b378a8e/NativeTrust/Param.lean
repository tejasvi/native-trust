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

Constants registered with `@[kernel_replace]` and the cast-free versions of the cast retry
(`NativeTrust.CastFree`) are roots as well. The decided term `e` becomes `E F h := e[…]`, and the kernel
proves
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
  /-- The retry (`CopyConfig.retryRepl`): definitions made roots because the kernel checks the equation of
  their generic version cheaply only by congruence (`genEqOf`), `c ↦ (replacement, theorem @c = @replacement)`. -/
  derived : NameMap (Name × Name) := {}
  /-- The retry: the equation of each generic version at the original roots (`genEqOf`), `c ↦ (g_orig,
  theorem @c = @g_orig)` with `g_orig := g o₁ rfl₁ …`, or `none`. -/
  geq : Std.HashMap Name (Option (Name × Name)) := {}

/-- The replaced constants: `orig ↦ (replacement, theorem @orig = @replacement)`. -/
abbrev Reps := NameMap (Name × Name)

/-- `System.Platform.numBits` as a root of its own (the platform case split, `proveTrueByKernelPlatform`). -/
theorem numBits_refl : @System.Platform.numBits = @System.Platform.numBits := rfl

abbrev PM := ReaderT (CopyConfig × Reps) (StateRefT PState MetaM)

def cfgM : PM CopyConfig := return (← read).1
/-- The replaced constants, and in the retry the definitions made roots on the way (`promote`). -/
def repsM : PM Reps := do
  let d := (← get).derived
  if d.isEmpty then return (← read).2
  return d.toList.foldl (fun m (k, v) => m.insert k v) (← read).2

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

/-- `T` where it agrees with `T'`, and `abst` applied to `T'` at the subterms where the two differ. -/
partial def diffTemplate (T T' : Expr) (abst : Expr → Expr) : Expr :=
  if T == T' then T else
  match T, T' with
  | .app f a, .app f' a' => .app (diffTemplate f f' abst) (diffTemplate a a' abst)
  | .lam n t b bi, .lam _ t' b' _ => .lam n (diffTemplate t t' abst) (diffTemplate b b' abst) bi
  | .forallE n t b bi, .forallE _ t' b' _ => .forallE n (diffTemplate t t' abst) (diffTemplate b b' abst) bi
  | .mdata _ e, _ => diffTemplate e T' abst
  | _, .mdata _ e' => diffTemplate T e' abst
  | .proj s i e, .proj _ j e' => if i == j then .proj s i (diffTemplate e e' abst) else abst T'
  | _, _ => abst T'

/-- `T = T'` for a proposition `T` and its rewrite `T'` (which mentions the `F`/`h` variables): at
`F := r, h := rfl` the rewrite unfolds to `T`, and dependent congruence along each `hᵢ` turns it into
`T'` (as `castProof` in `transportCopy`). When `T` itself mentions root variables (a field type of a
structure over a generic value: `(BitVec.ofNat F n).toNat < 2 ^ numBits` against `… < 2 ^ F`), the
congruence motive instantiates the roots only where `T` and `T'` differ (`diffTemplate`), so that it is `T`
at the original roots. -/
def castAlong (ctx : GenCtx) (T T' : Expr) : MetaM Expr := do
  let n := ctx.roots.size
  let vars := ctx.fs ++ ctx.hs
  let mentions := T.hasAnyFVar fun fv => vars.any (·.fvarId! == fv)
  let tmpl (xs : Array Expr) : Expr :=
    if mentions then diffTemplate T T' (·.replaceFVars vars xs) else T'.replaceFVars vars xs
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
        mkLambdaFVars #[y, hy] (tmpl (cf.set! i y ++ ch.set! i hy))
    let step := mkAppN (mkConst ``NativeTrust.congr_dep [ctx.levels[i]!, 1])
      #[ctx.types[i]!, mkSort levelZero, ctx.origs[i]!, Fi, ctx.fs[i]!, ctx.hs[i]!]
    curF := curF.set! i ctx.fs[i]!
    curH := curH.set! i ctx.hs[i]!
    let rhs := tmpl (curF ++ curH)
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

/-- `o₁ rfl₁ o₂ rfl₂ …`: the arguments of a generic version at the original roots. -/
def origArgs (roots : Array RootKey) : MetaM (Array Expr) := do
  let mut out := #[]
  for (rn, rls) in roots do
    let t := (← getConstInfo rn).instantiateTypeLevelParams rls
    let o := mkConst rn rls
    out := (out.push o).push (mkApp2 (mkConst ``Eq.refl [← getLevel t]) t o)
  return out

/-- Add `decl` with the kernel's check bounded by `hb` thousand heartbeats (`0`: the ambient bound); `false`,
with the environment as before, if the kernel rejects it or runs out. -/
def tryAddBounded (decl : Declaration) (hb : Nat) : MetaM Bool := do
  let env ← getEnv
  try
    if hb == 0 then addDeclSync decl
    else withOptions (fun o => maxHeartbeats.set o hb) (addDeclSync decl)
    return true
  catch _ =>
    setEnv env
    return false

/-- The retry: `c` becomes a root. Its replacement is its generic version at the replacements of its roots,
`c_r := g r₁' h₁' …`, and `@c = @c_r` follows from the equation `@c = @g_orig` (`genEqOf`) and dependent
congruence along those roots, as the bridge of the decided term does. -/
def promote (c : Name) (g : GenEntry) (eqName : Name) : PM Bool := do
  let env ← getEnv
  let some (.defnInfo ci) := env.find? c | return false
  let some (.defnInfo gi) := env.find? g.gen | return false
  let reps ← repsM
  let us := ci.levelParams.map mkLevelParam
  let n := g.roots.size
  let types ← g.roots.mapM fun (rn, rls) => return (← getConstInfo rn).instantiateTypeLevelParams rls
  let levels ← types.mapM fun t => (getLevel t : MetaM Level)
  let origs := g.roots.map fun (rn, rls) => mkConst rn rls
  let rfls := (Array.range n).map fun i => mkApp2 (mkConst ``Eq.refl [levels[i]!]) types[i]! origs[i]!
  let mut repls := #[]
  let mut eqs := #[]
  for (rn, rls) in g.roots do
    let some (r, h) := reps.find? rn | return false
    repls := repls.push (mkConst r rls)
    eqs := eqs.push (mkConst h rls)
  let args (xs hs : Array Expr) : Array Expr :=
    (Array.range n).foldl (fun acc i => (acc.push xs[i]!).push hs[i]!) #[]
  let gAt (xs hs : Array Expr) := mkAppN (mkConst g.gen us) (args xs hs)
  -- the generic version's type must not depend on the roots
  unless (← instantiateForall gi.type (args repls eqs)) == ci.type do return false
  let rName := g.gen ++ `_nt_rep
  let eName := g.gen ++ `_nt_repEq
  if env.contains rName || env.contains eName then return false
  let value := gAt repls eqs
  let hints := ReducibilityHints.regular (getMaxHeight env value + 1)
  let decl := Declaration.defnDecl { name := rName, levelParams := ci.levelParams, type := ci.type, value, hints, safety := .safe, all := [rName] }
  unless ← tryAddBounded decl 0 do return false
  let v ← getLevel ci.type
  let cE := mkConst c us
  -- `c = g_orig`, where `g_orig` is `g o rfl`, then along each root to its replacement
  let mut proof := mkConst eqName us
  let mut curX := origs
  let mut curH := rfls
  let mut lhs := gAt origs rfls
  for i in [0:n] do
    let (cx, ch) := (curX, curH)
    let eqTo (t : Expr) := mkApp3 (mkConst ``Eq [levels[i]!]) types[i]! origs[i]! t
    let Fi ← withLocalDeclD `y types[i]! fun y => withLocalDeclD `hy (eqTo y) fun hy =>
      mkLambdaFVars #[y, hy] (gAt (cx.set! i y) (ch.set! i hy))
    let step := mkAppN (mkConst ``NativeTrust.congr_dep [levels[i]!, v])
      #[types[i]!, ci.type, origs[i]!, Fi, repls[i]!, eqs[i]!]
    curX := curX.set! i repls[i]!
    curH := curH.set! i eqs[i]!
    let rhs := gAt curX curH
    proof := mkApp6 (mkConst ``Eq.trans [v]) ci.type cE lhs rhs proof step
    lhs := rhs
  let eqType := mkApp3 (mkConst ``Eq [v]) ci.type cE (mkConst rName us)
  let thm := Declaration.thmDecl { name := eName, levelParams := ci.levelParams, type := eqType, value := proof }
  unless ← tryAddBounded thm (← cfgM).rflHeartbeats do return false
  modify fun s => { s with derived := s.derived.insert c (rName, eName), needs := s.needs.insert c false }
  return true

/-- The equations `@c = @g_orig` of the generic versions that are not roots (`genEqOf`), for `transportCopy`. -/
def geqMap : PM (NameMap (Name × Name)) := do
  let st ← get
  return st.geq.fold (fun m d e? => match e? with
    | some e => if st.derived.contains d then m else m.insert d e
    | none => m) {}

/-- The retry (`CopyConfig.retryRepl`): the equation of the generic version `g` of `c` at the original roots,
`@c = @g_orig` with `g_orig := g o₁ rfl₁ …`. The kernel checks it by unfolding, bounded by
`CopyConfig.genEqHeartbeats`. That is cheap unless `c` applies a recursive function to literals: a structural
recursion on a literal fuel (`decodeTerm 4096 v`) is then unfolded level by level on both sides, and every
level has its recursive calls under binders, so the cost is exponential. Otherwise the equation comes from
dependent congruence along the equations of the generic versions that `c`'s value uses (`transportCopy`),
which compares the bodies once, and `c` becomes a root (`promote`): the generic definitions made after it
mention `c` itself, and no kernel check unfolds `g` at the original roots again. -/
def genEqOf (c : Name) (g : GenEntry) : PM Unit := do
  let env ← getEnv
  let cfg ← cfgM
  let some (.defnInfo ci) := env.find? c | return
  let some (.defnInfo gi) := env.find? g.gen | return
  let us := ci.levelParams.map mkLevelParam
  let args ← origArgs g.roots
  -- only when the generic version has `c`'s type at the original roots
  unless (← instantiateForall gi.type args) == ci.type do return
  let oName := g.gen ++ `_nt_orig
  let eqName := g.gen ++ `_nt_eq
  if env.contains oName || env.contains eqName then return
  let value := mkAppN (mkConst g.gen us) args
  let hints := ReducibilityHints.regular (getMaxHeight env value + 1)
  let decl := Declaration.defnDecl { name := oName, levelParams := ci.levelParams, type := ci.type, value, hints, safety := .safe, all := [oName] }
  unless ← tryAddBounded decl 0 do return
  let v ← getLevel ci.type
  let cE := mkConst c us
  let ty := mkApp3 (mkConst ``Eq [v]) ci.type cE (mkConst oName us)
  let t0 ← IO.monoMsNow
  let mkThm (pf : Expr) := Declaration.thmDecl { name := eqName, levelParams := ci.levelParams, type := ty, value := pf }
  if ← tryAddBounded (mkThm (mkApp2 (mkConst ``Eq.refl [v]) ci.type cE)) cfg.genEqHeartbeats then
    modify fun s => { s with geq := s.geq.insert c (some (oName, eqName)) }
    if cfg.trace then eprintRaw s!"NT param-geq {c} rfl ms={(← IO.monoMsNow) - t0}"
    return
  -- the equations of the generic versions in `c`'s value (promoted definitions occur as themselves)
  let eqs ← geqMap
  let t1 ← IO.monoMsNow
  let ok ← try
      match ← transportCopy ci.value ci.type eqs with
      | some (_, pf) => tryAddBounded (mkThm pf) cfg.rflHeartbeats
      | none => pure false
    catch _ => pure false
  if ok then
    modify fun s => { s with geq := s.geq.insert c (some (oName, eqName)) }
    let p ← promote c g eqName
    if cfg.trace then
      eprintRaw s!"NT param-geq {c} congr ms={(← IO.monoMsNow) - t1} rfl_ms={t1 - t0} root={p}"
  else
    modify fun s => { s with geq := s.geq.insert c none }
    if cfg.trace then eprintRaw s!"NT param-geq-none {c} ms={(← IO.monoMsNow) - t0}"

mutual

/-- The generic rewrite of `e` in `ctx`: roots become their variables, definitions that need generic
versions become `d.gen F h`, closed proofs and theorems whose types change are cast along the equations,
and values crossing a rigid inductive (its constructor types mention rewritten definitions) are coerced. -/
partial def genExpr (ctx : GenCtx) (fuel : Nat) (e : Expr) : PM Expr := do
  Meta.transform e
    (pre := fun e => do
      if e.isFVar || e.isSort || e.isBVar then return .continue
      -- read here: the retry makes definitions roots while rewriting (`promote`)
      let reps ← repsM
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
      let reps ← repsM
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
        let root : PM TransformStep := do
          let some i := ctx.find? (n, normLevels us)
            | modify (fun s => { s with missing := addRoot s.missing (n, normLevels us) })
              throwError "NativeTrust: parametric copy: root {n}.{us} is not abstracted here"
          return .done ctx.fs[i]!
        if reps.contains n then return ← root
        if !(← needsGen n) then return .done e
        let some g ← genConst n
          | throwError "NativeTrust: parametric copy: no generic version of {n}"
        -- the retry: `genConst` may have made `n` a root (`promote`)
        if (← repsM).contains n then return ← root
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
  -- the retry adds roots on the way (`promote`), each found by one more attempt
  let attempts := if cfg.retryRepl then 32 else 6
  for attempt in [0:attempts] do
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
      let decl := Declaration.defnDecl { name, levelParams := d.levelParams, type, value, hints,
                                         safety := .safe, all := [name] }
      -- bounded in the retry (`CopyConfig.copyHeartbeats`)
      if cfg.copyHeartbeats == 0 then addDeclSync decl
      else withOptions (fun o => maxHeartbeats.set o cfg.copyHeartbeats) (addDeclSync decl)
      if cfg.trace then eprintRaw s!"NT param-gen {c} roots={rs.size} ms={(← IO.monoMsNow) - t0}"
      let entry : GenEntry := { gen := name, roots := rs }
      modify fun s => { s with gens := s.gens.insert c (some entry), created := s.created.push name,
                               rootsMemo := s.rootsMemo.insert c rs }
      result := some entry
      -- the retry: the equation of the generic version, which can make `c` a root
      if cfg.retryRepl then
        try genEqOf c entry catch _ => pure ()
      break
    catch ex =>
      let miss := (← get).missing
      if !miss.isEmpty && attempt + 1 < attempts then
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
  /-- The retry: a proof of `e = e₀` where `e₀` is `e` with the definitions that have generic versions
  replaced by `g_orig` (`genEqOf`), which is `E r rfl` up to unfolding the `g_orig`. -/
  bridge? : Option Expr := none

def paramTerm (e : Expr) (cfg : CopyConfig) (castReps : Array (Name × Name × Name) := #[]) :
    MetaM ParamTerm := do
  let env ← getEnv
  let mut reps : Reps := {}
  if cfg.wf then reps := reps.insert ``WellFounded.fix (``NativeTrust.fixFuel, ``NativeTrust.fix_eq_fixFuel)
  for (f, g, thm) in (kernelReplaceExt.getState env).toList do
    reps := reps.insert f (g, thm)
  -- the retry with retry-only replacements (`CopyConfig.retryRepl`): they are roots as well
  if cfg.retryRepl then
    for (f, g, thm) in (kernelRetryReplaceExt.getState env).toList do
      reps := reps.insert f (g, thm)
  -- cast-free versions (the cast retry, `NativeTrust.CastFree`) are replaced like registered ones
  for (f, g, thm) in castReps do
    reps := reps.insert f (g, thm)
  let go : PM ParamTerm := do
    let mut roots ← rootsOfExpr e
    let attempts := if cfg.retryRepl then 32 else 6
    for attempt in [0:attempts] do
      modify fun s => { s with missing := #[] }
      let rootTypes ← roots.mapM fun (rn, rls) => do
        let some ci := (← getEnv).find? rn | throwError "unknown constant {rn}"
        return ci.instantiateTypeLevelParams rls
      let levels ← rootTypes.mapM fun t => (getLevel t : MetaM Level)
      let origs := roots.map fun (rn, rls) => mkConst rn rls
      let rfls := roots.mapIdx fun i _ => mkApp2 (mkConst ``Eq.refl [levels[i]!]) rootTypes[i]! origs[i]!
      let rs := roots
      try
        let E ← withRootVars rs rootTypes levels fun fs hs => do
          let ctx : GenCtx := { roots := rs, fs, hs, origs, rfls, types := rootTypes, levels }
          let e' ← genExpr ctx 8 e
          let vars := (Array.range rs.size).foldl (fun acc i => (acc.push fs[i]!).push hs[i]!) #[]
          mkLambdaFVars vars e'
        -- the roots now, with the definitions the retry made roots on the way
        let reps ← repsM
        let repls := rs.map fun (rn, rls) => mkConst (reps.find? rn).get!.1 rls
        let eqs := rs.map fun (rn, rls) => mkConst (reps.find? rn).get!.2 rls
        -- the retry: `e = e₀` by dependent congruence from the equations of the generic versions in `e`, so
        -- that the kernel does not unfold generic definitions at the original roots to see `e = E r rfl`
        let bridge? ← if !cfg.retryRepl then pure none else do
          let geqs ← geqMap
          if geqs.isEmpty then pure none else
          match ← (try transportCopy e (← inferType e) geqs catch _ => pure none) with
          | some (_, pf) => pure (some pf)
          | none => pure none
        let st ← get
        return { E, origs, rfls, repls, eqs, types := rootTypes, levels, created := st.created,
                 errors := st.errors, bridge? }
      catch ex =>
        let miss := (← get).missing
        if !miss.isEmpty && attempt + 1 < attempts then
          roots := miss.foldl addRoot roots
          continue
        throw ex
    throwError "NativeTrust: parametric route: the roots did not stabilize"
  (go.run (cfg, reps)).run' {}

end NativeTrust.Param
