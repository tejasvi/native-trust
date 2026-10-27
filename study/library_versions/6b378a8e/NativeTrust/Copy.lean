import Lean
import NativeTrust.Basic
import NativeTrust.StrFast
import NativeTrust.CSimpCompat

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

/-- A function that reads a string argument only through its character list:
`thm : ∀ x₁ … xₖ (s : String), f x₁ … xₖ s = g x₁ … xₖ s.toList`. -/
structure StrArgEntry where
  f : Name
  g : Name
  thm : Name
  /-- Number of arguments of `f`, the string included (it is the last one). -/
  arity : Nat
  deriving Inhabited

initialize strArgExt : SimpleScopedEnvExtension StrArgEntry (NameMap StrArgEntry) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun m e => m.insert e.f e
  }

/-- `@[kernel_string_arg] theorem thm : ∀ x₁ … xₖ (s : String), f x₁ … xₖ s = g x₁ … xₖ s.toList`:
when a decided term applies `f` to a string literal, or to a constant defined as one, NativeTrust
evaluates `g x₁ … xₖ [c₁, …, cₙ]` instead, so the kernel never builds or decodes the string (both
cost time and memory quadratic in its length). The rewrite is proved from `thm` and
`String.toList_ofList`, checked against the literal by the kernel's literal unfolding. -/
initialize registerBuiltinAttribute {
    name := `kernel_string_arg
    descr := "a function that reads its last (String) argument only through `String.toList`"
    add := fun decl _ kind => do
      let info ← getConstInfo decl
      unless info matches .thmInfo _ do
        throwError "@[kernel_string_arg]: `{decl}` must be a theorem"
      let entry ← MetaM.run' <| forallTelescope info.type fun xs body => do
        let bad : MetaM StrArgEntry := throwError "@[kernel_string_arg]: the statement must be \
          `∀ x₁ … xₖ (s : String), f x₁ … xₖ s = g x₁ … xₖ s.toList` for constants f, g"
        let some (_, lhs, rhs) := body.eq? | bad
        let .const f us := lhs.getAppFn | bad
        let .const g vs := rhs.getAppFn | bad
        if xs.isEmpty || us != vs || lhs.getAppArgs != xs then bad else
        let sv := xs.back!
        unless (← inferType sv) == mkConst ``String do discard bad
        let ra := rhs.getAppArgs
        unless ra.size == xs.size && ra.pop == xs.pop && ra.back! == mkApp (mkConst ``String.toList) sv do discard bad
        return { f, g, thm := decl, arity := xs.size }
      strArgExt.add entry kind
  }

/-- Replacements used only in the retry after the default attempts fail (`KernelConfig.foldRetry`):
`f ↦ (g, thm)` with `thm : @f = @g`, registered with `@[kernel_replace_retry]`. -/
initialize kernelRetryReplaceExt :
    SimpleScopedEnvExtension (Name × Name × Name) (NameMap (Name × Name)) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun m (f, g, thm) => m.insert f (g, thm)
  }

/-- `@[kernel_replace_retry] theorem thm : @f = @g` registers `g` as a replacement for `f` like
`@[kernel_replace]`, but only for the retry that runs after every default route has failed, when a
retry-only replacement or a `@[kernel_fold]` pattern is reachable. The default attempts never see it,
so a fact that converts without it is converted exactly as before (the string replacements of
`NativeTrust.StrLib` are registered this way: copying everything that reaches a `String` function can
cost more than the plain evaluation that already works). -/
initialize registerBuiltinAttribute {
    name := `kernel_replace_retry
    descr := "proof-carrying replacement used only in NativeTrust's retry with retry-only replacements"
    add := fun decl _ kind => do
      let info ← getConstInfo decl
      unless info matches .thmInfo _ do
        throwError "@[kernel_replace_retry]: `{decl}` must be a theorem `@f = @g`"
      match info.type.eq? with
      | some (_, .const f us, .const g vs) =>
        unless us == vs && us.all Level.isParam do
          throwError "@[kernel_replace_retry]: both sides must be the same universe-polymorphic constants"
        kernelRetryReplaceExt.add (f, g, decl) kind
      | _ => throwError "@[kernel_replace_retry]: the statement must be `@f = @g` for constants f, g"
  }

/-- A specialization pattern registered with `@[kernel_fold]`: definition `fn`, whose body applies `head`. -/
structure FoldEntry where
  head : Name
  fn : Name
  deriving Inhabited

initialize foldExt : SimpleScopedEnvExtension FoldEntry (NameMap (Array Name)) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun m e => m.insert e.head (((m.find? e.head).getD #[]).push e.fn)
  }

/-- The leading lambdas of `e` stripped: their number and the body (with loose bound variables). -/
partial def stripLams (e : Expr) (n : Nat := 0) : Nat × Expr :=
  match e with
  | .lam _ _ b _ => stripLams b (n + 1)
  | _ => (n, e)

/-- `@[kernel_fold] def F (x₁ … xₙ) := f a₁ … aₖ` marks `F` as a specialization of `f` (for instance
`f` applied to one type-class instance): in the retry with retry-only replacements (see
`kernel_replace_retry`), before NativeTrust copies a definition or evaluates a term, every occurrence
`f b₁ … bₖ` that matches `f a₁ … aₖ` (with the `xᵢ` as pattern variables) is folded into `F c₁ … cₙ`,
which is definitionally equal (unfold `F`, then β). With an equation `@F = @G` registered with
`@[kernel_replace_retry]` (or `@[kernel_replace]`), NativeTrust then evaluates `G` instead. This gives functions with type-class
arguments, such as `String.replace` with a `String` pattern, a replacement for one instance, which a
constant-level replacement of `f` (one equation for all instances) cannot express. -/
initialize registerBuiltinAttribute {
    name := `kernel_fold
    descr := "specialization pattern: occurrences of the body's application are folded into this definition"
    add := fun decl _ kind => do
      let some (.defnInfo d) := (← getEnv).find? decl
        | throwError "@[kernel_fold]: `{decl}` must be a definition"
      let (n, body) := stripLams d.value
      let .const f _ := body.getAppFn
        | throwError "@[kernel_fold]: the body of `{decl}` must be an application of a constant"
      if f == decl then throwError "@[kernel_fold]: `{decl}` must not apply itself"
      for i in [0:n] do
        unless body.hasLooseBVar i do
          throwError "@[kernel_fold]: every parameter of `{decl}` must occur in its body"
      foldExt.add { head := f, fn := decl } kind
  }

/-- Match `t` against the pattern `p` of a `@[kernel_fold]` definition with `n` parameters and level
parameters `lps`: loose bound variables `≥ depth` of `p` are the parameters (`depth` counts the binders
entered inside `p`). Returns the parameter values (by de Bruijn index) and the level parameter values. -/
partial def matchFold (n : Nat) (lps : List Name) (p t : Expr) :
    StateT (Array (Option Expr) × NameMap Level) Option Unit :=
  go p t 0
where
  goLvl (p t : Level) : StateT (Array (Option Expr) × NameMap Level) Option Unit := do
    match p with
    | .param u =>
      if lps.contains u then
        match (← get).2.find? u with
        | some l => unless l == t do failure
        | none => modify fun (a, m) => (a, m.insert u t)
      else unless t == p do failure
    | .succ p' => match t with
      | .succ t' => goLvl p' t'
      | _ => failure
    | .max p₁ p₂ => match t with
      | .max t₁ t₂ => do goLvl p₁ t₁; goLvl p₂ t₂
      | _ => failure
    | .imax p₁ p₂ => match t with
      | .imax t₁ t₂ => do goLvl p₁ t₁; goLvl p₂ t₂
      | _ => failure
    | _ => unless t == p do failure
  go (p t : Expr) (depth : Nat) : StateT (Array (Option Expr) × NameMap Level) Option Unit := do
    let t := t.consumeMData
    match p with
    | .bvar i =>
      if i < depth then
        unless t == .bvar i do failure
      else
        let j := i - depth
        unless j < n do failure
        -- the value must not mention the binders entered inside the pattern
        if (List.range depth).any t.hasLooseBVar then failure
        let v := t.lowerLooseBVars depth depth
        match (← get).1[j]! with
        | some u => unless u == v do failure
        | none => modify fun (a, m) => (a.set! j (some v), m)
    | .app pf pa => match t with
      | .app tf ta => do go pf tf depth; go pa ta depth
      | _ => failure
    | .const c ls => match t with
      | .const c' ls' =>
        unless c == c' && ls.length == ls'.length do failure
        for (l, l') in ls.zip ls' do goLvl l l'
      | _ => failure
    | .sort l => match t with
      | .sort l' => goLvl l l'
      | _ => failure
    | .lam _ ty b _ => match t with
      | .lam _ ty' b' _ => do go ty ty' depth; go b b' (depth + 1)
      | _ => failure
    | .forallE _ ty b _ => match t with
      | .forallE _ ty' b' _ => do go ty ty' depth; go b b' (depth + 1)
      | _ => failure
    | .letE _ ty v b _ => match t with
      | .letE _ ty' v' b' _ => do go ty ty' depth; go v v' depth; go b b' (depth + 1)
      | _ => failure
    | .mdata _ p' => go p' t depth
    | .proj S i p' => match t with
      | .proj S' i' t' => do
        unless S == S' && i == i' do failure
        go p' t' depth
      | _ => failure
    | _ => unless t == p do failure

/-- `t` folded into `F c₁ … cₙ` if it matches the pattern of the `@[kernel_fold]` definition `F`. -/
def tryFold (env : Environment) (F : Name) (t : Expr) : Option Expr := do
  let some (.defnInfo d) := env.find? F | none
  let (n, pat) := stripLams d.value
  -- an occurrence with more arguments than the pattern: fold its prefix
  let extra := t.getAppNumArgs - pat.getAppNumArgs
  let core := t.getAppPrefix (t.getAppNumArgs - extra)
  let ((), (asg, lasg)) ← (matchFold n d.levelParams pat core).run (Array.replicate n none, {})
  let us ← d.levelParams.mapM fun u => lasg.find? u
  let mut args := #[]
  for i in [0:n] do
    -- parameter `i` is bound variable `n - 1 - i` of the body
    args := args.push (← asg[n - 1 - i]!)
  return mkAppN (mkAppN (.const F us) args) (t.getAppArgs.extract (t.getAppNumArgs - extra) t.getAppNumArgs)

/-- `e` with every occurrence of a `@[kernel_fold]` pattern folded (innermost first), definitionally
equal to `e`. `self`: the definition whose body `e` is (a fold definition's own body is not folded into
itself). -/
partial def foldApps (env : Environment) (e : Expr) (self : Name := .anonymous) : Expr :=
  let reg := foldExt.getState env
  if reg.isEmpty then e
  else if !(e.find? fun | .const c _ => reg.contains c | _ => false).isSome then e
  else (go reg e).run' {}
where
  go (reg : NameMap (Array Name)) (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
    if let some r := (← get)[e]? then return r
    let r ← match e with
      | .app .. =>
        let e' ← e.withApp fun f args => do return mkAppN (← go reg f) (← args.mapM (go reg))
        match e'.getAppFn with
        | .const c _ => match reg.find? c with
          | some fns => pure ((fns.findSome? fun F => if F == self then none else tryFold env F e').getD e')
          | none => pure e'
        | _ => pure e'
      | .lam n t b bi => return .lam n (← go reg t) (← go reg b) bi
      | .forallE n t b bi => return .forallE n (← go reg t) (← go reg b) bi
      | .letE n t v b nd => return .letE n (← go reg t) (← go reg v) (← go reg b) nd
      | .mdata m b => return .mdata m (← go reg b)
      | .proj S i b => return .proj S i (← go reg b)
      | _ => pure e
    modify (·.insert e r)
    return r

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
  /-- Keep the original of a definition whose copy would equal it (no dependency could be copied).
  Needed when such a constant occurs in types (e.g. in a matcher's type), where abstracting it makes
  the congruence bridges ill-typed; off by default, since keeping the original changed which copies
  bridge in other packages (Strata). -/
  skipUnchanged : Bool := false
  /-- When the kernel rejects a copy, keep the proofs in its body as they are and transport them along
  the copy equations (`transportCopy`). Used by the retry of the fuel route
  (`proveTrueByKernel`): copies then get their own names and the shared registry is not used. -/
  transport : Bool := false
  /-- String literals of at least this many characters are rewritten in copies (and in the decided
  term) into `NativeTrust.ofListFast [c₁, …, cₙ]`, whose bytes the kernel builds in linear time
  (the kernel unfolds a literal to `String.ofList [c₁, …]`, whose `List.toByteArray` costs time and
  memory quadratic in the length). The equation is `ofList_eq_ofListFast`, checked against the
  literal by the kernel's own literal unfolding, without evaluation. `0` = off. -/
  fastLitMin : Nat := 128
  /-- Cast-free versions of definitions at whose casts an evaluation got stuck (`castFreeVersion?`):
  `(c, c', thm)` with `thm : @c = @c'`, used like registered replacements for the cast retry of an
  evaluation. Copies made with them get their own names (`castTag`), start from an empty registry and
  do not enter it, like the copies of the fuel route's retry. -/
  castReps : Array (Name × Name × Name) := #[]
  /-- Name tag of the copies made with `castReps` (`_ktc<hash>`, `t` appended with `transport`). -/
  castTag : Name := .anonymous
  /-- Never copy type formers (definitions of types, `Prop`-valued predicates, type-valued functions) or
  definitions of proofs. Evaluation never reduces them as data, but their copies occur in types: in the
  binder types of every definition that mentions them (`(h : BlockCtx.Valid blocks)`), where the copy makes
  the definition's copy ill-typed and the congruence bridges ill-typed. Kept as they are, they stay in the
  types of the copies, which then agree with the originals' types. Set by the fuel route's retry. -/
  keepTypes : Bool := false
  /-- The retry with retry-only replacements (`KernelConfig.foldRetry`): `@[kernel_fold]` patterns are
  folded and `@[kernel_replace_retry]` replacements apply; copies get their own names (`s` appended to
  the tag) and neither use nor enter the shared registry. -/
  retryRepl : Bool := false
  /-- `IO.monoMsNow` after which copying stops (the retry's time budget); `0` = none. -/
  deadline : Nat := 0
  /-- Heartbeat limit (thousands) for the kernel checks of copied definitions; `0` = the ambient
  option (as in the default attempts). -/
  copyHeartbeats : Nat := 0
  /-- The retry's parametric route: heartbeat limit (thousands) for the kernel's check, by unfolding, that a
  generic version at the original roots is its original (`Param.genEqOf`). -/
  genEqHeartbeats : Nat := 1000
  /-- Use the `@[csimp]` replacements of Mathlib and of the project (not those of Lean's core, which give
  tail-recursive or array-based versions for compiled code) as kernel replacements: a theorem
  `@f = @g` from the standard axioms between constants makes the kernel evaluate `g`, bridged by
  congruence like `@[kernel_replace]`. Mathlib's `Nat.choose = fast_choose` (Pascal's recursion vs. a
  product), `decidablePrime = decidablePrime'` (trial division up to the least factor) and the
  binary-splitting factorials are such replacements. -/
  csimp : Bool := false

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

/-- Distinct string literals of at least `minLen` characters in `e`, in order of appearance
(`minLen = 0`: none). -/
partial def collectLongLits (minLen : Nat) (e : Expr) : Array String :=
  if minLen == 0 then #[] else (go e).run ({}, #[]) |>.run.2.2
where
  go (e : Expr) : StateT (Std.HashSet Expr × Array String) Id Unit := do
    if (← get).1.contains e then return
    modify fun (v, o) => (v.insert e, o)
    match e with
    | .lit (.strVal str) =>
      if str.length ≥ minLen then modify fun (v, o) => (v, if o.contains str then o else o.push str)
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()

/-- Does `e` contain a string literal of at least `minLen` characters? -/
def hasLongLit (minLen : Nat) (e : Expr) : Bool :=
  minLen != 0 && (e.find? fun
    | .lit (.strVal str) => str.length ≥ minLen
    | _ => false).isSome

/-- The characters of a string literal as the kernel writes them when it unfolds the literal:
`[Char.ofNat c₁, …]` with raw natural-number literals. Built with a loop (literals can have a
million characters) and with one shared term per distinct character. -/
def charListExpr (str : String) : Expr := Id.run do
  let chars := str.toList.toArray
  let mut cache : Std.HashMap Nat Expr := {}
  let cons := mkApp (mkConst ``List.cons [levelZero]) (mkConst ``Char)
  let mut acc := mkApp (mkConst ``List.nil [levelZero]) (mkConst ``Char)
  let mut i := chars.size
  while 0 < i do
    i := i - 1
    let n := chars[i]!.toNat
    let c ← match cache[n]? with
      | some c => pure c
      | none =>
        let c := mkApp (mkConst ``Char.ofNat) (mkRawNatLit n)
        cache := cache.insert n c
        pure c
    acc := mkApp2 cons c acc
  return acc

/-- For each long literal of `e`: its fast form `ofListFast [c₁, …]` and the character list. -/
def longLitForms (minLen : Nat) (e : Expr) : Array (String × Expr × Expr) :=
  (collectLongLits minLen e).map fun str =>
    let l := charListExpr str
    (str, mkApp (mkConst ``NativeTrust.ofListFast) l, l)

/-- `e` with the given literals replaced by their fast forms. -/
def replaceLits (forms : Array (String × Expr × Expr)) (e : Expr) : Expr :=
  if forms.isEmpty then e else
  e.replace fun
    | .lit (.strVal str) => (forms.find? (·.1 == str)).map (·.2.1)
    | _ => none

/-- A proof of `e = e'`, with `e'` = `e` with the literals of `forms` replaced by their fast forms,
by congruence from `ofList_eq_ofListFast l : String.ofList l = ofListFast l`; the kernel checks
`String.ofList l ≡ "…"` by unfolding the literal (no evaluation). `type` is the type of `e`. -/
def litSubst (e type : Expr) (forms : Array (String × Expr × Expr)) : MetaM (Option (Expr × Expr)) := do
  let forms := forms.filter fun (str, _) => (e.find? fun
    | .lit (.strVal s') => s' == str
    | _ => false).isSome
  if forms.isEmpty then return none
  let strT := mkConst ``String
  let v ← getLevel type
  withLocalDeclsDND (forms.mapIdx fun i _ => ((`s).appendIndexAfter i, strT)) fun xs => do
    let M ← mkLambdaFVars xs <| e.replace fun
      | .lit (.strVal str) => (forms.findIdx? (·.1 == str)).map (xs[·]!)
      | _ => none
    let origs := forms.map fun (str, _) => mkStrLit str
    let tgts := forms.map (·.2.1)
    let mut args := origs
    let mut proof? : Option Expr := none
    let mut lhs := e
    for i in [0:forms.size] do
      let f ← withLocalDeclD `y strT fun y => mkLambdaFVars #[y] (mkAppN M (args.set! i y)).headBeta
      let h := mkApp (mkConst ``NativeTrust.ofList_eq_ofListFast) forms[i]!.2.2
      let step := mkApp6 (mkConst ``congrArg [1, v]) strT type origs[i]! tgts[i]! f h
      args := args.set! i tgts[i]!
      let rhs := (mkAppN M args).headBeta
      proof? := some <| match proof? with
        | none => step
        | some p => mkApp6 (mkConst ``Eq.trans [v]) type e lhs rhs p step
      lhs := rhs
    return proof?.map (·, lhs)

/-- The string a string argument stands for: a literal of at least `minLen` characters, or a
constant defined as one. -/
def strLitValue? (env : Environment) (minLen : Nat) : Expr → Option String
  | .lit (.strVal str) => if minLen != 0 && str.length ≥ minLen then some str else none
  | .const n _ => match env.find? n with
    | some (.defnInfo d) => match d.value with
      | .lit (.strVal str) => if minLen != 0 && str.length ≥ minLen then some str else none
      | _ => none
    | _ => none
  | _ => none

/-- Occurrences `f a₁ … aₖ c` in `e` of functions registered with `@[kernel_string_arg]`, applied to a
long literal `c` (or a constant defined as one). -/
partial def collectStrArgOccs (env : Environment) (reg : NameMap StrArgEntry) (minLen : Nat) (e : Expr) :
    Array (Expr × StrArgEntry × String) :=
  (go e).run ({}, #[]) |>.run.2.2
where
  go (e : Expr) : StateT (Std.HashSet Expr × Array (Expr × StrArgEntry × String)) Id Unit := do
    if (← get).1.contains e then return
    modify fun (v, o) => (v.insert e, o)
    match e with
    | .app .. =>
      if let .const f _ := e.getAppFn then
        if let some ent := reg.find? f then
          if e.getAppNumArgs == ent.arity then
            if let some str := strLitValue? env minLen e.appArg! then
              modify fun (v, o) => (v, o.push (e, ent, str))
              return
      e.withApp fun fn args => do go fn; for a in args do go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()

/-- Rewrite each occurrence `f a₁ … aₖ c` (see `collectStrArgOccs`) into `g a₁ … aₖ [c₁, …]`, with a
proof of `e = e'` by congruence: `thm a₁ … aₖ c : f … c = g … c.toList`, then
`String.toList_ofList : (String.ofList l).toList = l` read as `c.toList = l` (the kernel unfolds `c` to
its literal and the literal to `String.ofList l`; nothing is evaluated). `type` is the type of `e`. -/
def strArgSubst (e type : Expr) (minLen : Nat) : MetaM (Option (Expr × Expr)) := do
  let env ← getEnv
  let reg := strArgExt.getState env
  if reg.isEmpty || minLen == 0 then return none
  let occs := collectStrArgOccs env reg minLen e
  if occs.isEmpty then return none
  let v ← getLevel type
  let types ← occs.mapM fun (t, _) => inferType t
  let levels ← types.mapM getLevel
  let listChar := mkApp (mkConst ``List [levelZero]) (mkConst ``Char)
  withLocalDeclsDND (occs.mapIdx fun i _ => ((`a).appendIndexAfter i, types[i]!)) fun xs => do
    let M ← mkLambdaFVars xs <| e.replace fun t => (occs.findIdx? (·.1 == t)).map (xs[·]!)
    let origs := occs.map (·.1)
    let mut tgts := #[]
    let mut eqs := #[]
    for i in [0:occs.size] do
      let (t, ent, str) := occs[i]!
      let us := t.getAppFn.constLevels!
      let args := t.getAppArgs
      let c := args.back!
      let l := charListExpr str
      let gpre := mkAppN (mkConst ent.g us) args.pop
      let t' := mkApp gpre l
      let toListC := mkApp (mkConst ``String.toList) c
      let h1 := mkAppN (mkConst ent.thm us) args
      let h2 := mkApp6 (mkConst ``congrArg [1, levels[i]!]) listChar types[i]! toListC l gpre
        (mkApp (mkConst ``String.toList_ofList) l)
      tgts := tgts.push t'
      eqs := eqs.push (mkApp6 (mkConst ``Eq.trans [levels[i]!]) types[i]! t (mkApp gpre toListC) t' h1 h2)
    let mut args := origs
    let mut proof? : Option Expr := none
    let mut lhs := e
    for i in [0:occs.size] do
      let f ← withLocalDeclD `y types[i]! fun y => mkLambdaFVars #[y] (mkAppN M (args.set! i y)).headBeta
      let step := mkApp6 (mkConst ``congrArg [levels[i]!, v]) types[i]! type origs[i]! tgts[i]! f eqs[i]!
      args := args.set! i tgts[i]!
      let rhs := (mkAppN M args).headBeta
      proof? := some <| match proof? with
        | none => step
        | some p => mkApp6 (mkConst ``Eq.trans [v]) type e lhs rhs p step
      lhs := rhs
    return proof?.map (·, lhs)

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
  /-- Constants whose copy the kernel did not accept as `rfl`-equal, or whose copy would equal the
  original (kept as they are). -/
  failed : NameSet := {}
  /-- Copies created by this run, in dependency order. -/
  created : Array Name := #[]
  /-- Kernel time (ms) to check each copy and its equation, and whether the equation was proved by
  congruence (otherwise by `rfl`). -/
  timings : Array (Name × Nat × Nat × Bool) := #[]
  /-- Last kernel error of a congruence equation (diagnostics). -/
  lastCongrError : Option MessageData := none
  /-- `@[csimp]` replacements checked so far (`CopyConfig.csimp`). -/
  csimpOk : Std.HashMap Name Bool := {}

abbrev CopyM := ReaderT CopyConfig (StateRefT CopyState MetaM)

/-- Prefix for copies made here: `<decl>._kt` inside an asynchronous proof branch, otherwise
`_kt.<module>`. -/
def copyPrefix (wfAcc : Bool := false) (retry : Bool := false) (castTag : Name := .anonymous)
    (retryRepl : Bool := false) : CoreM Name := do
  let env ← getEnv
  -- copies made with the accessibility-generator route get their own names: they must never be
  -- mixed with fuel copies (their equations hold by `rfl` only among themselves); so do the copies
  -- of the fuel route's retry (`CopyConfig.transport`), which differ from the first attempt's, and
  -- those made with cast-free versions (`CopyConfig.castReps`), which differ for each set of them
  let tag := if wfAcc then `_kta else if !castTag.isAnonymous then castTag else if retry then `_ktt else `_kt
  -- and those of the retry with retry-only replacements (`CopyConfig.retryRepl`)
  let tag := if retryRepl then tag.appendAfter "s" else tag
  match env.asyncPrefix? with
  | some p => return p ++ tag
  | none => return tag ++ env.mainModule

/-- The copy registry may only be extended outside asynchronous branches. -/
def canRegister : CoreM Bool :=
  return (← getEnv).asyncPrefix?.isNone

def CopyState.init (env : Environment) (wf : Bool := true) (wfAcc : Bool := false)
    (fresh : Bool := false) (castReps : Array (Name × Name × Name) := #[]) (retryRepl : Bool := false) :
    CopyState :=
  -- the shared registry holds fuel copies; the accessibility-generator route and the fuel route's
  -- retry start afresh
  let reg := if wfAcc || fresh then {} else copyExt.getState env
  let user := kernelReplaceExt.getState env
  let subst := reg.foldl (fun m o e => m.insert o e.copy) {}
  let eqs := reg.foldl (fun m o e => m.insert o e.eq) {}
  let subst := user.foldl (fun m f (g, _) => m.insert f g) subst
  let eqs := user.foldl (fun m f (_, thm) => m.insert f thm) eqs
  let subst := castReps.foldl (fun m (f, g, _) => m.insert f g) subst
  let eqs := castReps.foldl (fun m (f, _, thm) => m.insert f thm) eqs
  -- the retry with retry-only replacements (`CopyConfig.retryRepl`)
  let retry := if retryRepl then kernelRetryReplaceExt.getState env else {}
  let subst := retry.foldl (fun m f (g, _) => m.insert f g) subst
  let eqs := retry.foldl (fun m f (_, thm) => m.insert f thm) eqs
  let (reps, reqs) := if wfAcc then (accReplacements, accEquations) else (baseReplacements, baseEquations)
  let subst := if wf then reps.foldl (fun m (a, b) => m.insert a b) subst else subst
  let eqs := if wf then reqs.foldl (fun m (a, b) => m.insert a b) eqs else eqs
  { subst, eqs }

/-- Is this definition a type former (its type is `Sort u` or `∀ xs, Sort u`: a type, a predicate, a
type-valued function) or a proof (its type is a proposition)? Such definitions are never evaluated as data
(`CopyConfig.keepTypes`). -/
def isTypeOrProofDef (d : DefinitionVal) : MetaM Bool := do
  try
    if ← isTypeFormerType d.type then return true
    isProp d.type
  catch _ => return false

/-- Does evaluating `g` possibly reach a constant without a kernel definition (an opaque constant, an
axiom other than the standard ones, an unsafe or `partial` definition)? Bounded breadth-first search
through definition bodies; `true` when unsure. Replacements made for compiled code often use hash maps,
arrays of machine words or tasks, which the kernel cannot evaluate. -/
def reachesOpaque (env : Environment) (g : Name) (limit : Nat := 5000) : Bool := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[g]
  let mut n := 0
  while h : 0 < todo.size do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    n := n + 1
    if n > limit then return true
    match env.find? c with
    -- `Lean.opaqueId` wraps the well-foundedness proofs of well-founded recursion: a proof, never evaluated
    | some (.opaqueInfo _) => if c != ``Lean.opaqueId then return true
    | some (.axiomInfo _) =>
      unless [``propext, ``Quot.sound, ``Classical.choice].contains c do return true
    | some (.defnInfo d) =>
      if d.safety != .safe then return true
      for dep in d.value.getUsedConstants do
        unless seen.contains dep do todo := todo.push dep
    | _ => pure ()
  return false

/-- With `CopyConfig.csimp`: if `c` has a usable `@[csimp]` replacement `thm : @c = @g` (a theorem from the
standard axioms, between constants with the same universe parameters, outside Lean's core), add it to
the replacements and return `true`. -/
def csimpReplacement (c : Name) : CopyM Bool := do
  if let some b := (← get).csimpOk[c]? then return b
  let env ← getEnv
  let ok ← match csimpEntry? env c with
    | none => pure false
    | some (g, thm) => do
      -- not Lean's core, and not Mathlib's `compile_inductive%` (implementations of recursors for the
      -- compiler, which the kernel evaluates natively)
      let core := match env.getModuleIdxFor? thm with
        | some i => match env.header.moduleNames[i.toNat]? with
          | some m => [`Init, `Std, `Lean].contains m.getRoot || m == `Mathlib.Util.CompileInductive
          | none => true
        | none => false
      -- only definitions are replaced (never a recursor, constructor or opaque constant); not the
      -- `Monoid.npow`/`AddMonoid.nsmul` defaults, which every algebraic instance reaches: replacing them
      -- copies the instances, and with them the types that mention them (`ZMod p`, curves)
      let isDefn := env.find? c matches some (.defnInfo _)
      let instanceDefault := [`npowRecAuto, `nsmulRecAuto, `npowRec, `nsmulRec].contains c
      if core || !isDefn || instanceDefault then pure false else
      match env.find? thm with
      | some (.thmInfo ti) =>
        match ti.type.eq? with
        | some (_, .const f us, .const g' vs) =>
          if f == c && g' == g && us == vs && us.all Level.isParam && env.contains g &&
              !reachesOpaque env g then
            let axs ← collectAxioms thm
            pure (axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·))
          else pure false
        | _ => pure false
      | _ => pure false
  modify fun s => { s with csimpOk := s.csimpOk.insert c ok }
  if ok then
    if let some (g, thm) := csimpEntry? env c then
      modify fun s => { s with subst := s.subst.insert c g, eqs := s.eqs.insert c thm }
  return ok

/-- Does constant `c` need a copy? Without `opt`: when evaluating it reaches a replaced constant.
With `opt`: every safe definition that is not inlined and not a kernel primitive. Only
definition bodies are followed: theorems are never evaluated, and opaque constants cannot be. -/
partial def needsCopy (c : Name) : CopyM Bool := do
  if (← get).subst.contains c then return true
  if (← read).csimp then
    if ← csimpReplacement c then return true
  if (← get).failed.contains c then return false
  if let some b := (← get).needs[c]? then return b
  -- provisional answer, in case of (impossible in the kernel) cycles
  modify fun s => { s with needs := s.needs.insert c false }
  let cfg ← read
  let env ← getEnv
  let r ← match env.find? c with
    | some (.defnInfo d) =>
      if d.safety != .safe || kernelPrimitives.contains c || uncopyable.contains c then pure false
      -- types, predicates and proofs: kept as they are (they occur in types, see `CopyConfig.keepTypes`)
      else if cfg.keepTypes && (← isTypeOrProofDef d) then pure false
      -- a long string literal in the body: the copy holds its fast form (`CopyConfig.fastLitMin`)
      else if hasLongLit cfg.fastLitMin d.value then pure true
      -- the retry with retry-only replacements: a `@[kernel_fold]` pattern in the body, folded in the copy
      else if cfg.retryRepl && foldApps env d.value c != d.value then pure true
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

/-- `@c = @copy` for a definition `c` whose value is not a function (a closed piece of data, such as
`def x : Bool := match f y with …`), by congruence through an auxiliary motive constant. To check `c = value`
by unfolding, the kernel unfolds the abbreviation at the head of the value (a matcher) before `c`, and then
evaluates the closed discriminant (`whnf` of a recursor's major premise): the plain congruence equation of
minidregg's `enrolledCarry` timed out that way. Here `G := fun xs => value[xs]` gets `c`'s reducibility
hints, so the kernel unfolds `c` and `G origs` together (and `G copies` and the copy, which has `c`'s hints
too) and compares the results syntactically. `none` if no constant is replaced or the kernel rejects the
motive. -/
def congrViaMotive (c copyName : Name) (d : DefinitionVal) (eqs : NameMap (Name × Name)) :
    MetaM (Option Expr) := do
  let body := d.value
  let occs := (collectOccs eqs body).toArray
  if occs.isEmpty then return none
  let env ← getEnv
  let types ← occs.mapM fun (c, us) => do
    let some ci := env.find? c | throwError "unknown constant {c}"
    return ci.instantiateTypeLevelParams us
  let levels ← types.mapM getLevel
  let u ← getLevel d.type
  let M ← withLocalDeclsDND (occs.mapIdx fun i _ => ((`x).appendIndexAfter i, types[i]!)) fun xs =>
    mkLambdaFVars xs <| body.replace fun
      | .const c us => (occs.findIdx? (· == (c, us))).map (xs[·]!)
      | _ => none
  let gName := copyName ++ `_motive
  let envB ← getEnv
  try
    let gType ← inferType M
    let gDecl : DefinitionVal := { d with name := gName, type := gType, value := M, all := [gName] }
    addDeclSync <| .defnDecl gDecl
  catch _ =>
    setEnv envB
    return none
  let us := d.levelParams.map mkLevelParam
  let G := mkConst gName us
  let origs := occs.map fun (c, us) => mkConst c us
  let copies := occs.map fun (c, us) => mkConst (eqs.find? c).get!.1 us
  -- `Eq.refl c` read as `c = G origs`: same hints, unfolded together
  let mut proof := mkApp2 (mkConst ``Eq.refl [u]) d.type (mkConst c us)
  let mut args := origs
  let mut lhs := mkAppN G origs
  for i in [0:occs.size] do
    let (cn, cus) := occs[i]!
    let h := mkConst (eqs.find? cn).get!.2 cus
    let a := args
    let f ← withLocalDeclD `y types[i]! fun y => mkLambdaFVars #[y] (mkAppN G (a.set! i y))
    let step := mkApp6 (mkConst ``congrArg [levels[i]!, u]) types[i]! d.type origs[i]! copies[i]! f h
    args := args.set! i copies[i]!
    let rhs := mkAppN G args
    proof := mkApp6 (mkConst ``Eq.trans [u]) d.type (mkConst c us) lhs rhs proof step
    lhs := rhs
  return some proof

/-- `@a.{us} = @b.{us}` for constants `a`, `b` of the same type. -/
def mkConstEq (a b : Name) (lvls : List Name) (type : Expr) : MetaM Expr := do
  let us := lvls.map mkLevelParam
  let u ← getLevel type
  return mkApp3 (mkConst ``Eq [u]) type (mkConst a us) (mkConst b us)

/-- `congrSubst` with given replacements: for `targets` mapping `(cᵢ, us)` to `(tᵢ, hᵢ)` with
`hᵢ : @cᵢ.{us} = tᵢ` (any terms, e.g. free variables), a proof of `e = e'` and `e'`, the term `e` with
these occurrences replaced; `none` if there is none. -/
def congrSubstWith (e type : Expr) (targets : Array ((Name × List Level) × Expr × Expr)) :
    MetaM (Option (Expr × Expr)) := do
  let names : NameMap Unit := targets.foldl (fun m ((c, _), _) => m.insert c ()) {}
  let occs := (collectOccs names e).toArray.filter fun o => targets.any (·.1 == o)
  if occs.isEmpty then return none
  let find (o : Name × List Level) : Expr × Expr := ((targets.find? (·.1 == o)).getD (o, default, default)).2
  let env ← getEnv
  let types ← occs.mapM fun (c, us) => do
    let some ci := env.find? c | throwError "unknown constant {c}"
    return ci.instantiateTypeLevelParams us
  let levels ← types.mapM getLevel
  let v ← getLevel type
  withLocalDeclsDND (occs.mapIdx fun i _ => ((`x).appendIndexAfter i, types[i]!)) fun xs => do
    let M ← mkLambdaFVars xs <| e.replace fun
      | .const c us => (occs.findIdx? (· == (c, us))).map (xs[·]!)
      | _ => none
    let origs := occs.map fun (c, us) => mkConst c us
    let tgts := occs.map fun o => (find o).1
    let mut args := origs
    let mut proof? : Option Expr := none
    let mut lhs := e
    for i in [0:occs.size] do
      let f ← withLocalDeclD `y types[i]! fun y =>
        mkLambdaFVars #[y] (mkAppN M (args.set! i y)).headBeta
      let step := mkApp6 (mkConst ``congrArg [levels[i]!, v]) types[i]! type origs[i]! tgts[i]! f
        (find occs[i]!).2
      args := args.set! i tgts[i]!
      let rhs := (mkAppN M args).headBeta
      proof? := some <| match proof? with
        | none => step
        | some p => mkApp6 (mkConst ``Eq.trans [v]) type e lhs rhs p step
      lhs := rhs
    return proof?.map (·, lhs)

/-- The transform of `transportCopy`: the constants `occs[i]` become the free variables `xs[i]`; a proof
whose type mentions them is cast along `castProof` to the transform of its type, which may itself hold
proofs (inside a subtype value, say), so that every cast stays well-typed for all values of the `xs`.
`fuel` bounds the nesting of proofs inside types (below it, a cast along plain congruence). -/
partial def transportGo (occs : Array (Name × List Level)) (xs hs : Array Expr)
    (castProof : Expr → Expr → MetaM Expr) (fuel : Nat) (e : Expr) : MetaM Expr :=
  Meta.transform e
    (pre := fun e => do
      if e.isFVar || e.isSort || e.isBVar then return .continue
      let isPf ← try isProof e catch _ => pure false
      unless isPf do return .continue
      let T ← inferType e
      let mentions := (T.find? fun
        | .const c _ => occs.any (·.1 == c)
        | _ => false).isSome
      unless mentions do return .done e
      if fuel == 0 then
        match ← congrSubstWith T (mkSort levelZero) (occs.mapIdx fun i o => (o, xs[i]!, hs[i]!)) with
        | some (hT, T') => return .done (mkApp4 (mkConst ``Eq.mp [levelZero]) T T' hT e)
        | none => return .done e
      let T' ← transportGo occs xs hs castProof (fuel - 1) T
      if T' == T then return .done e
      return .done (mkApp4 (mkConst ``Eq.mp [levelZero]) T T' (← castProof T T') e))
    (post := fun e => match e with
      | .const c us => match occs.findIdx? (· == (c, us)) with
        | some i => return .done xs[i]!
        | none => return .done e
      | _ => return .done e)

/-- The value of a fuel copy whose body holds proofs that mention copied constants, and a proof of
`body = value`. Example: `Multiset.sort` is `Quot.liftOn s (fun l => mergeSort l r) p` with `p` a
proof about `mergeSort`, and `Nat.find h` comes with `Nat.find_spec h`. A fuel copy equals its
original only propositionally, so substituting inside such a proof makes it ill-typed (the kernel
then rejects the copy), and the congruence motive that abstracts it is ill-typed as well. Here every
proof is kept as it is and transported along the equations (`Eq.mp`), and `body = value` is proved
by dependent congruence (`congr_dep`, one constant at a time): its motive also takes the equation,
so the transported proofs stay well-typed for every value of the abstracted constant. -/
def transportCopy (body type : Expr) (eqs : NameMap (Name × Name)) :
    MetaM (Option (Expr × Expr)) := do
  let occs := (collectOccs eqs body).toArray
  if occs.isEmpty then return none
  let env ← getEnv
  let types ← occs.mapM fun (c, us) => do
    let some ci := env.find? c | throwError "unknown constant {c}"
    return ci.instantiateTypeLevelParams us
  let levels ← types.mapM getLevel
  let v ← getLevel type
  let origs := occs.map fun (c, us) => mkConst c us
  let copies := occs.map fun (c, us) => mkConst (eqs.find? c).get!.1 us
  let eqPfs := occs.map fun (c, us) => mkConst (eqs.find? c).get!.2 us
  let eqTo (i : Nat) (t : Expr) := mkApp3 (mkConst ``Eq [levels[i]!]) types[i]! origs[i]! t
  withLocalDeclsDND (occs.mapIdx fun i _ => ((`x).appendIndexAfter i, types[i]!)) fun xs => do
  withLocalDeclsDND (occs.mapIdx fun i _ => ((`h).appendIndexAfter i, eqTo i xs[i]!)) fun hs => do
    let rfls := occs.mapIdx fun i _ => mkApp2 (mkConst ``Eq.refl [levels[i]!]) types[i]! origs[i]!
    -- `T = T'` for a proposition `T` and its transform `T'` (constants abstracted, nested proofs
    -- transported): `T'` with every `xᵢ := cᵢ, hᵢ := rfl` is `T` up to proof irrelevance, and dependent
    -- congruence along each `hᵢ` turns it into `T'`
    let castProof (T T' : Expr) : MetaM Expr := do
      let mut proof := mkApp2 (mkConst ``Eq.refl [1]) (mkSort levelZero) T
      let mut curX := origs
      let mut curH := rfls
      let mut lhs := T
      for i in [0:occs.size] do
        unless T'.containsFVar xs[i]!.fvarId! || T'.containsFVar hs[i]!.fvarId! do
          curX := curX.set! i xs[i]!; curH := curH.set! i hs[i]!
          continue
        let (cx, ch) := (curX, curH)
        let Fi ← withLocalDeclD `y types[i]! fun y =>
          withLocalDeclD `hy (eqTo i y) fun hy =>
            mkLambdaFVars #[y, hy] (T'.replaceFVars (xs ++ hs) (cx.set! i y ++ ch.set! i hy))
        let step := mkAppN (mkConst ``NativeTrust.congr_dep [levels[i]!, 1])
          #[types[i]!, mkSort levelZero, origs[i]!, Fi, xs[i]!, hs[i]!]
        curX := curX.set! i xs[i]!
        curH := curH.set! i hs[i]!
        let rhs := T'.replaceFVars (xs ++ hs) (curX ++ curH)
        proof := mkApp6 (mkConst ``Eq.trans [1]) (mkSort levelZero) T lhs rhs proof step
        lhs := rhs
      return proof
    let bodyXH ← transportGo occs xs hs castProof 8 body
    let F ← mkLambdaFVars (xs ++ hs) bodyXH
    let value := F.beta (copies ++ eqPfs)
    let start := F.beta (origs ++ rfls)
    let mut curX := origs
    let mut curH := rfls
    let mut lhs := start
    -- `body = F origs rfls`: they differ only in proofs (proof irrelevance)
    let mut proof := mkApp2 (mkConst ``Eq.refl [v]) type body
    for i in [0:occs.size] do
      let (cx, ch) := (curX, curH)
      let Fi ← withLocalDeclD `y types[i]! fun y =>
        withLocalDeclD `hy (eqTo i y) fun hy =>
          mkLambdaFVars #[y, hy] (F.beta (cx.set! i y ++ ch.set! i hy))
      let step := mkAppN (mkConst ``NativeTrust.congr_dep [levels[i]!, v])
        #[types[i]!, type, origs[i]!, Fi, copies[i]!, eqPfs[i]!]
      curX := curX.set! i copies[i]!
      curH := curH.set! i eqPfs[i]!
      let rhs := F.beta (curX ++ curH)
      proof := mkApp6 (mkConst ``Eq.trans [v]) type body lhs rhs proof step
      lhs := rhs
    return some (value, proof)

/-- `x` with the kernel's heartbeat limit set to `hb` thousand heartbeats (`0`: unchanged), for the kernel
checks of copied definitions in the retry with retry-only replacements. -/
def withCopyHeartbeats {α : Type} (hb : Nat) (x : CopyM α) : CopyM α :=
  if hb == 0 then x else withOptions (fun o => maxHeartbeats.set o hb) x

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
  -- the retry's time budget (`CopyConfig.deadline`)
  if cfg.deadline != 0 && (← IO.monoMsNow) > cfg.deadline then
    throwError "NativeTrust: the retry with retry-only replacements ran out of its time budget \
      while copying `{c}` (`KernelConfig.retryMs`)"
  let name := (← copyPrefix cfg.wfAcc cfg.transport cfg.castTag cfg.retryRepl) ++ c
  let eqName := name ++ `_eq
  let body ← if cfg.opt then inlineSimp env cfg d.value else pure d.value
  -- the retry: `@[kernel_fold]` patterns, definitionally equal, so `c = body` still holds by `rfl`
  let body := if cfg.retryRepl then foldApps env body c else body
  -- kernel checks of copied definitions: bounded in the retry (`CopyConfig.copyHeartbeats`)
  let bounded := withCopyHeartbeats (α := Unit) cfg.copyHeartbeats
  for dep in body.getUsedConstants do
    if dep != c && (← needsCopy dep) then discard <| copyConst dep
  -- an earlier call in this module may already have made it
  if !env.contains name then
    let value₁ := substConsts (← get).subst body
    -- long string literals become `ofListFast [c₁, …]`, with `litPf : value₁ = value`
    let forms := longLitForms cfg.fastLitMin value₁
    let (value, litPf?) ← if forms.isEmpty then pure (value₁, none) else
      match ← litSubst value₁ d.type forms with
      | some (h, v) => pure (v, some h)
      | none => pure (value₁, none)
    -- nothing was replaced (the dependencies that needed copies could not be copied): the copy would
    -- be the original under another name, so keep the original. A needless replacement is harmful:
    -- a constant that occurs in types (e.g. in the type of a matcher, `Val ctx.primCtx`) makes the
    -- congruence bridges ill-typed when it is abstracted
    if cfg.skipUnchanged && value == d.value then
      if cfg.trace then eprintRaw s!"NT copy-unchanged {c}"
      modify fun s => { s with failed := s.failed.insert c }
      return none
    let envBefore ← getEnv
    try
      if cfg.trace then eprintRaw s!"NT copying {c}"
      let t0 ← IO.monoMsNow
      bounded <| addDeclSync <| .defnDecl { d with name, value, all := [name] }
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
      let trans (b c' : Expr) (h₁ h₂ : Expr) := mkApp6 (mkConst ``Eq.trans [u]) d.type (mkConst c us) b c' h₁ h₂
      let viaCongr ← match ← congrSubst body d.type depEqs, litPf? with
        | some h, none => pure <| some (trans body value refl h)
        | some h, some hl =>
          let u' := u
          pure <| some (mkApp6 (mkConst ``Eq.trans [u']) d.type (mkConst c us) value₁ value
            (trans body value₁ refl h) hl)
        | none, some hl => pure <| some (trans body value refl hl)
        | none, none => pure none
      let mkEq (v : Expr) : Declaration :=
        .thmDecl { name := eqName, levelParams := d.levelParams, type := eqType, value := v }
      let tryEq (pf : Expr) (tag : String) : CopyM Bool := do
        let envB ← getEnv
        try
          withOptions (fun o => maxHeartbeats.set o cfg.rflHeartbeats) (addDeclSync (mkEq pf))
          pure true
        catch ex =>
          setEnv envB
          modify fun s => { s with lastCongrError := some m!"{c}: {ex.toMessageData}" }
          if cfg.trace then
            let m := (← ex.toMessageData.toString).replace "\n" " "
            eprintRaw s!"NT {tag} {c}: {m.take 700}"
          pure false
      -- a closed piece of data: first through a motive constant with `c`'s hints (`congrViaMotive`),
      -- which keeps the kernel from evaluating the value while it compares `c` with it
      let okMotive ← if d.value.isLambda || litPf?.isSome || cfg.opt then pure false else do
        -- over the body as copied (folded in the retry), which is definitionally equal to `d.value`
        match ← (try withCopyHeartbeats cfg.copyHeartbeats (congrViaMotive c name { d with value := body } depEqs)
            catch _ => pure none) with
        | some pf => tryEq pf "copy-motive-rejected"
        | none => pure false
      let ok ← if okMotive then pure true else match viaCongr with
        | some pf => tryEq pf "copy-congr-rejected"
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
    catch exCopy =>
      setEnv envBefore
      if cfg.trace then
        let m := (← exCopy.toMessageData.toString).replace "\n" " "
        eprintRaw s!"NT copy-rejected {c}: {m.take 700}"
      -- fuel route: the body may hold proofs about copied constants; transport them instead
      let ok ← if cfg.wfAcc || !cfg.transport then pure false else do
        let st ← get
        let depEqs : NameMap (Name × Name) := st.subst.foldl (fun m o r =>
          match st.eqs.find? o with | some h => m.insert o (r, h) | none => m) {}
        let t0 ← IO.monoMsNow
        try
          let some (value', pf) ← transportCopy body d.type depEqs | pure false
          bounded <| addDeclSync <| .defnDecl { d with name, value := value', all := [name] }
          let t1 ← IO.monoMsNow
          let us := d.levelParams.map mkLevelParam
          let u ← getLevel d.type
          let refl := mkApp2 (mkConst ``Eq.refl [u]) d.type (mkConst c us)
          let pf := mkApp6 (mkConst ``Eq.trans [u]) d.type (mkConst c us) body value' refl pf
          let eqType ← mkConstEq c name d.levelParams d.type
          withOptions (fun o => maxHeartbeats.set o cfg.rflHeartbeats) <| addDeclSync <|
            .thmDecl { name := eqName, levelParams := d.levelParams, type := eqType, value := pf }
          let t2 ← IO.monoMsNow
          modify fun s => { s with timings := s.timings.push (c, t1 - t0, t2 - t1, true) }
          if cfg.trace then eprintRaw s!"NT copy-transport {c} defn_ms={t1 - t0} eq_ms={t2 - t1}"
          pure true
        catch ex =>
          setEnv envBefore
          modify fun s => { s with lastCongrError := some m!"{c} (transport): {ex.toMessageData}" }
          if cfg.trace then
            let m := (← ex.toMessageData.toString).replace "\n" " "
            eprintRaw s!"NT copy-failed {c}: {m.take 700}"
          pure false
      unless ok do
        modify fun s => { s with failed := s.failed.insert c }
        return none
    if (← canRegister) && !cfg.wfAcc && !cfg.transport && cfg.castReps.isEmpty && !cfg.retryRepl then
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
  (go.run cfg).run' (CopyState.init (← getEnv) cfg.wf cfg.wfAcc
    (cfg.transport || !cfg.castReps.isEmpty || cfg.retryRepl) cfg.castReps cfg.retryRepl)

end NativeTrust
