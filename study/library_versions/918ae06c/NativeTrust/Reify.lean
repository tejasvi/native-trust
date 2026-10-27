import Lean

/-!
# Values of compiled evaluations as expressions

`reifyValue t T` evaluates the closed term `t : T` with compiled code and turns the result into an
expression built from constructors and literals. The result is an untrusted hint: it is only ever
used as the right-hand side of an equation `t = v` that the kernel checks by evaluation (staged
evaluation in `NativeTrust.Kernel`), so a wrong value costs a failed check, never soundness.

For the type of the value (and every type nested in it) a serializer `Array Expr → T → Expr` is
generated as an `unsafe` definition (`casesOn` on the value, one case per constructor), compiled and
run:
* `Nat` becomes a raw literal; `String`, `Int`, `Rat`, `Bool`, `Char`, `Unit`, fixed-width integers,
  `Fin n` and `BitVec n` use their `ToExpr` instances; `List`, `Array` and `ByteArray` are serialized
  iteratively (no deep recursion);
* a field that is a proof becomes `of_decide_eq_true inst (Eq.refl true)` for its statement
  instantiated with the other fields, with a `Decidable` instance found when the serializer is
  generated: the kernel decides each such statement when it checks the value;
* functions, types, opaque types (`Float`, `USize`), indexed families and data fields whose type
  depends on other data fields are not supported (the value is then not reified).

The serializers and the runner are added in `withoutModifyingEnv`, so nothing persists.
-/

open Lean Meta

namespace NativeTrust

/-- `[x₁, …, xₙ]`, built from the right without deep recursion (`cons`, `nil` already applied to the
element type). -/
def listToExprWith {β : Type} (cons nil : Expr) (f : β → Expr) (xs : List β) : Expr :=
  xs.reverse.foldl (fun acc x => mkApp2 cons (f x) acc) nil

/-- `Array.mk [x₁, …, xₙ]` (`mk`, `cons`, `nil` already applied to the element type). -/
def arrayToExprWith {β : Type} (mk cons nil : Expr) (f : β → Expr) (xs : Array β) : Expr :=
  mkApp mk (xs.foldr (fun x acc => mkApp2 cons (f x) acc) nil)

/-- `ByteArray.mk (Array.mk [b₁, …, bₙ])`, each byte by `f`. -/
def byteArrayToExprWith (bmk mk cons nil : Expr) (f : UInt8 → Expr) (b : ByteArray) : Expr :=
  mkApp bmk (arrayToExprWith mk cons nil f b.data)

/-- Entry `k` of the table of closed expressions that a generated serializer refers to. -/
def stashGet (env : Array Expr) (k : Nat) : Expr := env.getD k (.bvar 0)

def emptyExprs : Array Expr := #[]

def pushExpr (a : Array Expr) (e : Expr) : Array Expr := a.push e

def instRevExprs (e : Expr) (a : Array Expr) : Expr := e.instantiateRev a

def mkAppExprs (f : Expr) (a : Array Expr) : Expr := mkAppN f a

/-- `of_decide_eq_true inst (Eq.refl true) : p`. -/
def mkDecideProof (p inst : Expr) : Expr :=
  mkApp3 (mkConst ``of_decide_eq_true) p inst
    (mkApp2 (mkConst ``Eq.refl [(Level.succ Level.zero)]) (mkConst ``Bool) (mkConst ``Bool.true))

/-- Types whose values are serialized by their `ToExpr` instance. -/
def reifyBuiltinHeads : List Name :=
  [``String, ``Int, ``Rat, ``Bool, ``Char, ``Unit, ``UInt8, ``UInt16, ``UInt32, ``UInt64,
   ``Int8, ``Int16, ``Int32, ``Int64, ``Fin, ``BitVec]

/-- Types that are never reified: no constructors usable at run time, platform-dependent, or not data. -/
def reifyRefused : List Name :=
  [``Float, ``Float32, ``USize, ``ISize, ``Thunk, ``Task, ``FloatArray, ``IO.Ref, ``ST.Ref,
   ``Lean.Expr, ``Lean.Environment]

structure ReifyState where
  /-- closed type ↦ index of its serializer -/
  idx : Std.HashMap Expr Nat := {}
  /-- types with a serializer, by index -/
  types : Array Expr := #[]
  /-- the serializers' bodies, by index (`none` while being generated) -/
  bodies : Array (Option Expr) := #[]
  /-- closed expressions the generated code refers to (`stashGet env k`) -/
  stash : Array Expr := #[]
  stashIdx : Std.HashMap Expr Nat := {}
  /-- names of the serializers -/
  names : Array Name := #[]
  base : Name := .anonymous

abbrev ReifyM := StateRefT ReifyState MetaM

/-- The term `stashGet env k` for a closed expression `e` (stored once). -/
def stashTerm (env : Expr) (e : Expr) : ReifyM Expr := do
  let s ← get
  let k ← match s.stashIdx[e]? with
    | some k => pure k
    | none =>
      let k := s.stash.size
      set { s with stash := s.stash.push e, stashIdx := s.stashIdx.insert e k }
      pure k
  return mkApp2 (mkConst ``stashGet) env (mkRawNatLit k)

def exprT : Expr := mkConst ``Lean.Expr

def arrayExprT : Expr := mkApp (mkConst ``Array [Level.zero]) exprT

/-- Index of the serializer of the closed type `T` (generated later). -/
def serIndex (T : Expr) : ReifyM Nat := do
  let s ← get
  if let some k := s.idx[T]? then return k
  let k := s.types.size
  set { s with idx := s.idx.insert T k, types := s.types.push T, bodies := s.bodies.push none,
               names := s.names.push (s.base ++ (`s).appendIndexAfter k) }
  return k

/-- `T` as an inductive type applied to closed parameters: `(I, us, params)`. -/
def inductiveHead? (T : Expr) : MetaM (Option (InductiveVal × List Level × Array Expr)) := do
  let .const n us := T.getAppFn | return none
  let some (.inductInfo iv) := (← getEnv).find? n | return none
  if iv.numIndices != 0 || T.getAppNumArgs != iv.numParams then return none
  return some (iv, us, T.getAppArgs)

/-- The term (of type `Expr`) serializing `f : A`, with `env` the table of the generated code. -/
partial def fieldSer (env : Expr) (A : Expr) (f : Expr) : ReifyM Expr := do
  let A ← whnf A
  if A.hasFVar || A.hasLooseBVars || A.hasMVar then
    throwError "reify: a field type depends on other fields or variables:{indentExpr A}"
  if A.isConstOf ``Nat then return mkApp (mkConst ``Lean.mkRawNatLit) f
  let .const head us := A.getAppFn
    | throwError "reify: not an inductive type:{indentExpr A}"
  if reifyRefused.contains head then throwError "reify: type `{head}` is not supported"
  if head == ``List && A.getAppNumArgs == 1 then
    let α := A.getAppArgs[0]!
    let u := us.headD Level.zero
    let cons ← stashTerm env (mkApp (mkConst ``List.cons [u]) α)
    let nil ← stashTerm env (mkApp (mkConst ``List.nil [u]) α)
    let g ← withLocalDeclD `y α fun y => do mkLambdaFVars #[y] (← fieldSer env α y)
    return mkAppN (mkConst ``listToExprWith) #[α, cons, nil, g, f]
  if head == ``Array && A.getAppNumArgs == 1 then
    let α := A.getAppArgs[0]!
    let u := us.headD Level.zero
    let mk ← stashTerm env (mkApp (mkConst ``Array.mk [u]) α)
    let cons ← stashTerm env (mkApp (mkConst ``List.cons [u]) α)
    let nil ← stashTerm env (mkApp (mkConst ``List.nil [u]) α)
    let g ← withLocalDeclD `y α fun y => do mkLambdaFVars #[y] (← fieldSer env α y)
    return mkAppN (mkConst ``arrayToExprWith) #[α, mk, cons, nil, g, f]
  if head == ``ByteArray then
    let u8 := mkConst ``UInt8
    let bmk ← stashTerm env (mkConst ``ByteArray.mk)
    let mk ← stashTerm env (mkApp (mkConst ``Array.mk [Level.zero]) u8)
    let cons ← stashTerm env (mkApp (mkConst ``List.cons [Level.zero]) u8)
    let nil ← stashTerm env (mkApp (mkConst ``List.nil [Level.zero]) u8)
    let g ← withLocalDeclD `y u8 fun y => do mkLambdaFVars #[y] (← fieldSer env u8 y)
    return mkAppN (mkConst ``byteArrayToExprWith) #[bmk, mk, cons, nil, g, f]
  if reifyBuiltinHeads.contains head then
    let lvl ← getLevel A
    let u ← match lvl.dec with
      | some u => pure u
      | none => throwError "reify: unexpected universe of{indentExpr A}"
    let inst ← synthInstance (mkApp (mkConst ``Lean.ToExpr [u]) A)
    return mkAppN (mkConst ``Lean.ToExpr.toExpr [u]) #[A, inst, f]
  let some _ ← inductiveHead? A
    | throwError "reify: `{head}` is not an inductive type without indices"
  let k ← serIndex A
  return mkApp2 (mkConst (← get).names[k]!) env f

/-- The body of one `casesOn` alternative: the fields from `i` on, with `acc` the array of the
expressions of the fields before `i` (let-bound, so that each is computed once). -/
partial def genAltGo (env ctorE : Expr) (c : Name) (fields : Array Expr) (i : Nat) (acc : Expr)
    (lets : Array Expr) : ReifyM Expr := do
  if h : i < fields.size then
    let f := fields[i]
    let A ← inferType f
    let prev := fields.extract 0 i
    let e ← if ← isProp A then do
        if A.hasAnyFVar (fun fv => !prev.contains (.fvar fv)) then
          throwError "reify: a proof field of `{c}` mentions later fields"
        let inst ← try synthInstance (mkApp (mkConst ``Decidable) A)
          catch _ => throwError "reify: no Decidable instance for a proof field of `{c}`:{indentExpr A}"
        let tyT ← stashTerm env (A.abstract prev)
        let instT ← stashTerm env ((← instantiateMVars inst).abstract prev)
        pure (mkApp2 (mkConst ``mkDecideProof)
          (mkApp2 (mkConst ``instRevExprs) tyT acc) (mkApp2 (mkConst ``instRevExprs) instT acc))
      else
        if A.hasAnyFVar (fun fv => prev.contains (.fvar fv)) then
          throwError "reify: a field type of `{c}` depends on another field"
        fieldSer env A f
    withLetDecl ((`e).appendIndexAfter i) exprT e fun ev =>
      withLetDecl ((`a).appendIndexAfter i) arrayExprT (mkApp2 (mkConst ``pushExpr) acc ev) fun av =>
        genAltGo env ctorE c fields (i + 1) av (lets.push ev |>.push av)
  else
    mkLetFVars lets (mkApp2 (mkConst ``mkAppExprs) ctorE acc)

/-- Generate the serializer body for the `k`-th type. -/
def genSer (k : Nat) : ReifyM Unit := do
  let T := (← get).types[k]!
  let some (iv, us, ps) ← inductiveHead? T
    | throwError "reify: not an inductive type without indices:{indentExpr T}"
  if iv.ctors.isEmpty then throwError "reify: `{iv.name}` has no constructors"
  if (← getLevel T).isZero then throwError "reify: `{iv.name}` is a proposition"
  let body ← withLocalDeclD `env arrayExprT fun env => withLocalDeclD `x T fun x => do
    let motive ← withLocalDeclD `t T fun t => mkLambdaFVars #[t] exprT
    let mut alts := #[]
    for c in iv.ctors do
      let cinfo ← getConstInfoCtor c
      let cty ← instantiateForall (cinfo.type.instantiateLevelParams cinfo.levelParams us) ps
      let ctorE ← stashTerm env (mkAppN (mkConst c us) ps)
      let alt ← forallTelescope cty fun fields _ => do
        if fields.size != cinfo.numFields then
          throwError "reify: unexpected constructor type of `{c}`"
        let b ← genAltGo env ctorE c fields 0 (mkConst ``emptyExprs) #[]
        mkLambdaFVars fields b
      alts := alts.push alt
    let cases := mkAppN (mkConst (mkCasesOnName iv.name) ((Level.succ Level.zero) :: us))
      ((ps.push motive).push x ++ alts)
    mkLambdaFVars #[env, x] cases
  modify fun s => { s with bodies := s.bodies.set! k (some body) }

/-- An `unsafe` definition without universe parameters. -/
def mkUnsafeDefn (name : Name) (type value : Expr) (all : List Name) : DefinitionVal :=
  { name := name, levelParams := [], type := type, value := value, hints := ReducibilityHints.opaque,
    safety := DefinitionSafety.unsafe, all := all }

/-- Generate all pending serializers. -/
def genAllSers : ReifyM Unit := do
  let mut i := 0
  while i < (← get).types.size do
    genSer i
    i := i + 1

/-- Time (ms) of the compiled evaluation in the last `reifyValue` (without compilation): a hint of how
expensive the term is. -/
initialize lastReifyEvalMs : IO.Ref Nat ← IO.mkRef 0

/-- Evaluate the closed term `t : T` with compiled code and return its value as an expression (an
untrusted hint), or the reason why it could not be reified. -/
def reifyValue (t T : Expr) : MetaM (Except String Expr) := do
  if t.hasFVar || t.hasMVar || T.hasFVar || T.hasMVar ||
      !(collectLevelParams {} t).params.isEmpty || !(collectLevelParams {} T).params.isEmpty then
    return .error "not closed (variables or universe parameters)"
  withoutModifyingEnv do
    let base ← mkAuxDeclName `_kt_reify
    let act : ReifyM Name := do
      let runBody ← withLocalDeclD `env arrayExprT fun env => do
        mkLambdaFVars #[env] (← fieldSer env T t)
      genAllSers
      let s ← get
      let decls := (List.range s.types.size).map fun j =>
        mkUnsafeDefn s.names[j]! (mkForall `env BinderInfo.default arrayExprT
            (mkForall `x BinderInfo.default s.types[j]! exprT)) s.bodies[j]!.get! s.names.toList
      let runner := base ++ `run
      let runDecl := Declaration.defnDecl (mkUnsafeDefn runner
        (mkForall `env BinderInfo.default arrayExprT exprT) runBody [runner])
      for d in decls do modifyEnv (markMeta · d.name)
      modifyEnv (markMeta · runner)
      withOptions (fun o => ((Elab.async.set o false).insert `compiler.postponeCompile (.ofBool false)).insert
          `compiler.relaxedMetaCheck (.ofBool true)) do
        unless decls.isEmpty do addAndCompile (.mutualDefnDecl decls)
        addAndCompile runDecl
      return runner
    try
      let (runner, s) ← act.run { base }
      let f ← unsafe evalConst (Array Expr → Expr) runner
      let t0 ← IO.monoMsNow
      let v := f s.stash
      -- force the value before reading the clock (it is computed lazily otherwise)
      let n := v.approxDepth
      lastReifyEvalMs.set ((← IO.monoMsNow) - t0 + (if n == 0 then 0 else 0))
      return .ok v
    catch ex =>
      return .error (← ex.toMessageData.toString)

/-- Can values of type `T` be reified? Generates the serializers only (nothing is evaluated). -/
def reifiable (T : Expr) : MetaM Bool := do
  if T.hasFVar || T.hasMVar || !(collectLevelParams {} T).params.isEmpty then return false
  let act : ReifyM Unit := do
    withLocalDeclD `env arrayExprT fun env => withLocalDeclD `x T fun x => do
      discard <| fieldSer env T x
    genAllSers
  try
    discard <| act.run { base := `_kt_reify_check }
    return true
  catch _ => return false

end NativeTrust
