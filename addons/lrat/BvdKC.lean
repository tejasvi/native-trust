import Lean
import Std.Tactic.BVDecide
/-!
# BvdKC: a kernel-evaluable copy of the `bv_decide` checking pipeline

`bv_decide`'s bitblaster, AIG-to-CNF relabelling and LRAT checker use `Std.HashMap`/`DHashMap`.
The kernel cannot evaluate them: bucket indices go through `USize`, whose width is the opaque
`System.Platform.getNumBits`, and the derived `Hashable` instances call the opaque C primitive
`mixHash`.

An `opaque` constant is uninterpreted in the logic: the kernel never unfolds it, so every
declaration that mentions it stays type-correct when it is replaced by any closed term of the same
type. This file copies every declaration in the dependency cone of the soundness chain
(`BVLogicalExpr.unsat_of_bitblast`, `Entrypoint.relabelNat_unsat_iff`, `toCNF_equisat`,
`LRAT.check_sound`) that mentions `mixHash` or `getNumBits` (transitively), under the prefix `KC.`,
with those two constants replaced by the definitions `BvdKC.mix` and `BvdKC.numBits64` below.
Definitions, theorems (proofs included) and inductive types are re-added and re-checked by the
kernel; nothing is assumed. Declarations outside the cone (e.g. `BVLogicalExpr`, `CNF.Unsat`,
`IntAction`) are shared, so the copied soundness theorems conclude statements about the original
types.
-/
open Lean Meta Elab Command

namespace BvdKC

/-- Kernel stand-in for `mixHash` (any function of this type is sound). -/
def mix (a b : UInt64) : UInt64 := a * 1099511628211 + b

/-- Kernel stand-in for `System.Platform.getNumBits` (the logic only knows the value is 32 or 64). -/
def numBits64 (_ : Unit) : { n : Nat // n = 32 ∨ n = 64 } := ⟨64, Or.inr rfl⟩

def roots : List Name := [``Std.Tactic.BVDecide.BVLogicalExpr.unsat_of_bitblast,
  ``Std.Sat.AIG.Entrypoint.relabelNat_unsat_iff, ``Std.Sat.AIG.toCNF_equisat,
  ``Std.Tactic.BVDecide.LRAT.check_sound, ``Std.Tactic.BVDecide.LRAT.check, ``Std.Sat.AIG.toCNF,
  ``Std.Sat.AIG.Entrypoint.relabelNat, ``Std.Tactic.BVDecide.BVLogicalExpr.bitblast]

def standIns : List (Name × Name) :=
  [(``mixHash, ``BvdKC.mix), (``System.Platform.getNumBits, ``BvdKC.numBits64)]

def pfx : Name := `KC

partial def projAsConst (e : Expr) : Expr := e.replace fun
  | .proj s _ b => some (mkApp (mkConst s) (projAsConst b))
  | _ => none

def usedNames (e : Expr) : Array Name := (projAsConst e).getUsedConstants

partial def rename (m : NameMap Name) (e : Expr) : Expr := e.replace fun
  | .const n ls => (m.find? n).map (mkConst · ls)
  | .proj s i b => match m.find? s with
    | some s' => some (.proj s' i (rename m b))
    | none => none
  | _ => none

def depsOf (env : Environment) (c : Name) : Array Name := Id.run do
  let some ci := env.find? c | return #[]
  let mut s := usedNames ci.type
  if let some v := ci.value? (allowOpaque := true) then s := s ++ usedNames v
  match ci with
  | .inductInfo i =>
    s := s ++ i.ctors.toArray ++ i.all.toArray
    for ct in i.ctors do
      if let some cc := env.find? ct then s := s ++ usedNames cc.type
  | .ctorInfo i => s := s.push i.induct
  | .recInfo i => s := s ++ i.all.toArray
  | _ => pure ()
  return s

structure St where
  map : NameMap Name := {}
  visiting : NameSet := {}
  tainted : NameSet := {}
  count : Nat := 0
  kernelMs : Nat := 0
  slow : Array (Nat × Name) := #[]

abbrev M := StateRefT St CoreM

def timedAdd (c : Name) (decl : Declaration) : M Unit := do
  let t0 ← IO.monoMsNow
  withOptions (Elab.async.set · false) (addDecl decl)
  let dt := (← IO.monoMsNow) - t0
  modify fun s => { s with kernelMs := s.kernelMs + dt, count := s.count + 1,
                           slow := if dt ≥ 200 then s.slow.push (dt, c) else s.slow }

def mkPlainDecl (ci : ConstantInfo) (m : NameMap Name) : CoreM Declaration := do
  let n' := pfx ++ ci.name
  let ty := rename m ci.type
  match ci with
  | .defnInfo d => return Declaration.defnDecl ({ d with name := n', type := ty, value := rename m d.value, all := d.all.map (pfx ++ ·) })
  | .thmInfo d => return Declaration.thmDecl ({ d with name := n', type := ty, value := rename m d.value, all := d.all.map (pfx ++ ·) })
  | .opaqueInfo d => return Declaration.opaqueDecl ({ d with name := n', type := ty, value := rename m d.value, all := d.all.map (pfx ++ ·) })
  | _ => throwError "BvdKC: unexpected constant kind {ci.name}"

/-- The unit a constant is added with: an inductive block (represented by its first type) or itself. -/
def unitOf (env : Environment) (c : Name) : Name :=
  match env.find? c with
  | some (.ctorInfo i) => match env.find? i.induct with
    | some (.inductInfo j) => j.all.head!
    | _ => i.induct
  | some (.recInfo i) => i.all.head!
  | some (.inductInfo i) => i.all.head!
  | _ => c

def unitMembers (env : Environment) (u : Name) : Array Name :=
  match env.find? u with
  | some (.inductInfo i) => i.all.foldl (fun acc n => match env.find? n with
      | some (.inductInfo j) => (acc.push n) ++ j.ctors.toArray
      | _ => acc.push n) #[]
  | _ => #[u]

def copyPlain (c : Name) : M Unit := do
  let ci ← getConstInfo c
  let decl ← mkPlainDecl ci (← get).map
  try timedAdd c decl
  catch ex => throwError "BvdKC: kernel rejected copy of {c}: {ex.toMessageData}"
  modify fun s => { s with map := s.map.insert c (pfx ++ c) }

def copyInduct (i : InductiveVal) : M Unit := do
  let env ← getEnv
  let infos ← i.all.mapM fun n => do
    match env.find? n with
    | some (.inductInfo j) => pure j
    | _ => throwError "BvdKC: {n} is not an inductive"
  let m0 := (← get).map
  let m := infos.foldl (fun m j =>
    j.ctors.foldl (fun m ct => m.insert ct (pfx ++ ct)) (m.insert j.name (pfx ++ j.name))) m0
  let types ← infos.mapM fun j => do
    let ctors ← j.ctors.mapM fun ct => do
      pure ({ name := pfx ++ ct, type := rename m (← getConstInfo ct).type } : Constructor)
    pure ({ name := pfx ++ j.name, type := rename m j.type, ctors } : InductiveType)
  try timedAdd i.name (.inductDecl i.levelParams i.numParams types i.isUnsafe)
  catch ex => throwError "BvdKC: kernel rejected copy of inductive {i.name}: {ex.toMessageData}"
  let env' ← getEnv
  let mut m := m
  for j in infos do
    m := m.insert (j.name ++ `rec) (pfx ++ j.name ++ `rec)
    for k in [1:20] do
      let r := j.name ++ Name.mkSimple s!"rec_{k}"
      if env'.contains (pfx ++ r) then m := m.insert r (pfx ++ r)
  modify fun s => { s with map := m }

def copyUnit (u : Name) : M Unit := do
  match (← getEnv).find? u with
  | some (.inductInfo i) => copyInduct i
  | _ => copyPlain u

/-- Copy the tainted cone of `roots`. -/
def run : CoreM St := do
  let env ← getEnv
  -- closure
  let mut seen : NameSet := {}
  let mut stack := roots.toArray
  let mut order : Array Name := #[]
  while h : stack.size > 0 do
    let c := stack.back
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    order := order.push c
    for d in depsOf env c do
      unless seen.contains d do stack := stack.push d
  IO.eprintln s!"BvdKC: closure {order.size}"
  let deps : Std.HashMap Name (Array Name) := order.foldl (fun m c => m.insert c (depsOf env c)) {}
  let mut tainted : NameSet := standIns.foldl (fun s (n, _) => s.insert n) {}
  let mut changed := true
  while changed do
    changed := false
    for c in order do
      if tainted.contains c then continue
      if (deps.getD c #[]).any tainted.contains then
        tainted := tainted.insert c; changed := true
  IO.eprintln s!"BvdKC: tainted {tainted.size}"
  let map0 : NameMap Name := standIns.foldl (fun m (a, b) => m.insert a b) {}
  -- units and their dependencies (iterative DFS post-order = topological order)
  let isStand (c : Name) := standIns.any (·.1 == c)
  let unitDeps (u : Name) : Array Name := Id.run do
    let mut r : Array Name := #[]
    for mem in unitMembers env u do
      for d in depsOf env mem do
        if tainted.contains d && !isStand d then
          let du := unitOf env d
          if du != u then r := r.push du
    return r
  let mut done : NameSet := {}
  let mut topo : Array Name := #[]
  let rootUnits := (roots.filter tainted.contains).map (unitOf env)
  for r in rootUnits do
    if done.contains r then continue
    let mut st : Array (Name × Array Name × Nat) := #[(r, unitDeps r, 0)]
    let mut onStack : NameSet := ({} : NameSet).insert r
    while h : st.size > 0 do
      let (u, ds, i) := st.back
      if i < ds.size then
        st := st.set! (st.size - 1) (u, ds, i + 1)
        let d := ds[i]!
        unless done.contains d || onStack.contains d do
          st := st.push (d, unitDeps d, 0)
          onStack := onStack.insert d
      else
        st := st.pop
        onStack := onStack.erase u
        done := done.insert u
        topo := topo.push u
  IO.eprintln s!"BvdKC: units {topo.size}"
  let (_, st) ← (do
      let mut k := 0
      for u in topo do
        if k < 30 then IO.eprintln s!"BvdKC: unit {u}"
        copyUnit u
        k := k + 1
        if k % 250 == 0 then IO.eprintln s!"BvdKC: {k}/{topo.size} units"
    : M Unit).run { map := map0, tainted }
  return st

elab "#bvd_kc_copy" : command => do
  let t0 ← IO.monoMsNow
  let st ← liftCoreM run
  let dt := (← IO.monoMsNow) - t0
  let slow := (st.slow.qsort (fun a b => a.1 > b.1)).toList.take 12
  logInfo m!"BvdKC: copied {st.count} declarations ({st.tainted.size} tainted incl. stand-ins), \
    kernel {st.kernelMs} ms, total {dt} ms; slowest: {slow}"

end BvdKC

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
#bvd_kc_copy
