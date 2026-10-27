import NativeTrust
import BvdKC
import LratBits
import LratAdapter
import Std.Tactic.BVDecide
/-!
# Driver: `bv_decide` facts through the bitmask LRAT checker

For a theorem `t` whose proof contains `Reflect.unsat_of_verifyBVExpr_eq_true E C ax`:
- compiled code parses the certificate `C` (untrusted) and converts it to `LratBits.BAct` steps,
  stored as definitions `t._kb_c<i>` (chunks) and `t._kb_acts`;
- the kernel evaluates `checkBits (toL (KC.toCNF (KC.relabelNat (KC.bitblast E)))) t._kb_acts`
  (NativeTrust `proveTrueByKernel`).

Commands: `#kb_size t` (sizes, compiled code only), `kb_check t` (kernel check of the certificate),
`kb_cnf t` (kernel evaluation of the CNF alone, for timing).
-/
open Lean Meta Elab Command
open Std.Tactic.BVDecide

namespace LratBits

def natLit (n : Nat) : Expr := .lit (.natVal n)

def natListExpr (l : List Nat) : Expr :=
  l.foldr (fun n acc => mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Nat) (natLit n) acc)
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Nat))

/-- Bitmasks of an LRAT clause (literal `±v` is CNF atom `v - 1`). -/
def clauseMasks (c : Array Int) : Nat × Nat :=
  c.foldl (fun (acc : Nat × Nat) (l : Int) =>
    if l > 0 then (acc.1 ||| (1 <<< (l.natAbs - 1)), acc.2)
    else if l < 0 then (acc.1, acc.2 ||| (1 <<< (l.natAbs - 1)))
    else acc) (0, 0)

def pairListExpr (l : List (Nat × Nat)) : Expr :=
  let ty := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst ``Nat)
  l.foldr (fun (a, b) acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty
      (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst ``Nat) (natLit a) (natLit b)) acc)
    (mkApp (mkConst ``List.nil [Level.zero]) ty)

def single (x : Nat) : Bool := x != 0 && (x &&& (x - 1)) == 0

/-- Compiled-code replay of the kernel checker on the clause list `F` (same semantics): converts
the steps to `BAct` data and annotates every hint with the variable it makes unit (`0` when it
does not). Deletions are dropped (sound for RUP; the kernel checker ignores them too), RAT steps
become `unsupported`. Returns the steps, the number of RAT steps, and the replay's verdict. -/
def annotate (F : List (List (Nat × Bool))) (acts : Array LRAT.IntAction) :
    Array (Option (Nat × Nat × Nat × Array (Nat × Nat))) × Nat × Bool := Id.run do
  let mut store : Std.HashMap Nat (Nat × Nat) := {}
  let mut i := 1
  for c in F do
    store := store.insert i (litsBits c 0 0)
    i := i + 1
  let mut out : Array (Option (Nat × Nat × Nat × Array (Nat × Nat))) := #[]
  let mut rat := 0
  let mut verdict := false
  let mut failed := false
  for a in acts do
    let info : Option (Nat × Nat × Nat × Array Nat) := match a with
      | .addEmpty id hints => some (id, 0, 0, hints)
      | .addRup id c hints => let m := clauseMasks c; some (id, m.1, m.2, hints)
      | _ => none
    match a with
    | .addRat .. => rat := rat + 1; out := out.push none; continue
    | _ => pure ()
    let some (id, cp, cn, hints) := info | continue
    -- replay the propagation
    let mut ann : Array (Nat × Nat) := #[]
    let mut ok := false
    if (cp &&& cn) != 0 then
      ok := true
      ann := hints.map (·, 0)
    else
      let mut pa := cn
      let mut na := cp
      let mut done := false
      for h in hints do
        if done then ann := ann.push (h, 0); continue
        match store.get? h with
        | none => ann := ann.push (h, 0)
        | some (hp, hn) =>
          if ((hp &&& pa) ||| (hn &&& na)) != 0 then ann := ann.push (h, 0)
          else
            let up := hp ^^^ (hp &&& (pa ||| na))
            let un := hn ^^^ (hn &&& (pa ||| na))
            if up == 0 && un == 0 then ann := ann.push (h, 0); done := true; ok := true
            else if up == 0 && single un then ann := ann.push (h, Nat.log2 un); na := na ||| un
            else if un == 0 && single up then ann := ann.push (h, Nat.log2 up); pa := pa ||| up
            else ann := ann.push (h, 0)
    out := out.push (some (id, cp, cn, ann))
    if !ok then failed := true; break
    if (cp ||| cn) == 0 then
      verdict := true
      break
    store := store.insert id (cp, cn)
  return (out, rat, verdict)

def listExpr (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [Level.zero]) ty)

def stringOfConst (e : Expr) : MetaM String := do
  let .const n _ := e | throwError "kb: certificate is not a constant: {e}"
  let some v := (← getConstInfo n).value? | throwError "kb: {n} has no value"
  let .lit (.strVal s) := v | throwError "kb: {n} is not a string literal"
  return s

/-- All `unsat_of_verifyBVExpr_eq_true E C ax` subterms of `v`. -/
def collectVerify (v : Expr) : Array Expr := Id.run do
  let mut acc : Array Expr := #[]
  let mut todo : Array Expr := #[v]
  let mut seen : Std.HashSet Expr := {}
  while h : todo.size > 0 do
    let e := todo.back
    todo := todo.pop
    if seen.contains e then continue
    seen := seen.insert e
    if e.isAppOfArity ``Reflect.unsat_of_verifyBVExpr_eq_true 3 then acc := acc.push e; continue
    match e with
    | .app f a => todo := (todo.push f).push a
    | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
    | .letE _ t x b _ => todo := ((todo.push t).push x).push b
    | .mdata _ b => todo := todo.push b
    | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return acc

def valueOf (n : Name) : MetaM Expr := do
  let ci ← getConstInfo n
  match ci with
  | .thmInfo t => pure t.value
  | _ => match ci.value? (allowOpaque := true) with
    | some v => pure v
    | none => throwError "kb: {n} has no value"

/-- `KC.toCNF (KC.relabelNat (KC.bitblast E))`. -/
def cnfExpr (E : Expr) : Expr :=
  let entry := mkApp (mkConst ``KC.Std.Tactic.BVDecide.BVLogicalExpr.bitblast) E
  let relab := mkApp4 (mkConst ``KC.Std.Sat.AIG.Entrypoint.relabelNat) (mkConst ``BVBit)
    (mkConst ``instDecidableEqBVBit) (mkConst ``KC.Std.Tactic.BVDecide.instHashableBVBit) entry
  mkApp (mkConst ``KC.Std.Sat.AIG.toCNF) relab

/-- A checksum that forces every literal of a clause list (for timing the CNF alone). -/
def cnfSum (F : List (List (Nat × Bool))) : Nat :=
  F.foldl (fun acc c => c.foldl (fun a l => cond l.2 (a + l.1 + 1) (a + l.1)) (acc + 7)) 0

/-- A hint list as an expression of bounded depth: lists longer than 500 are split into
constants `base._kb_h<i>` joined by `List.append`. -/
def hintsExpr (base : Name) (ann : Array (Nat × Nat)) (naux : Nat) : MetaM (Expr × Nat) := do
  let piece := 500
  if ann.size ≤ piece then return (pairListExpr ann.toList, naux)
  let pty := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst ``Nat)
  let plty := mkApp (mkConst ``List [Level.zero]) pty
  let mut parts : Array Expr := #[]
  let mut j := 0
  let mut n := naux
  while j < ann.size do
    let nm := base ++ Name.mkSimple s!"_kb_h{n}"
    n := n + 1
    let dv : DefinitionVal := { name := nm, levelParams := [], type := plty, value := pairListExpr (ann.extract j (j + piece)).toList, hints := .abbrev, safety := .safe }
    addDecl (.defnDecl dv)
    parts := parts.push (mkConst nm)
    j := j + piece
  return (parts.pop.foldr (fun p acc => mkApp3 (mkConst ``List.append [Level.zero]) pty p acc) parts.back!, n)

/-- Define the certificate of `E`/`C` as chunked `BAct` lists; returns the name of the list of chunks. -/
def defineActs (base : Name) (E C : Expr) (chunk : Nat := 2000) : MetaM (Name × Nat × Nat × Nat) := do
  let s ← stringOfConst C
  let t0 ← IO.monoMsNow
  let acts ← match LRAT.parseLRATProof s.toUTF8 with
    | .ok a => pure a
    | .error err => throwError "kb: the certificate does not parse: {err}"
  let bv ← unsafe evalExpr BVLogicalExpr (mkConst ``BVLogicalExpr) E
  let F := toL (Std.Sat.AIG.toCNF bv.bitblast.relabelNat)
  let (steps, rat, verdict) := annotate F acts
  unless verdict do logInfo m!"kb: the compiled replay of the checker does not accept the certificate"
  let tParse := (← IO.monoMsNow) - t0
  let mut naux := 0
  let mut exprs : Array Expr := #[]
  for st in steps do
    match st with
    | none => exprs := exprs.push (mkConst ``BAct.unsupported)
    | some (id, cp, cn, ann) =>
      -- long hint lists: pieces of 500 hints as separate constants, joined by `List.append`
      let (hl, naux') ← hintsExpr base ann naux
      naux := naux'
      exprs := exprs.push (mkApp4 (mkConst ``BAct.rup) (natLit id) (natLit cp) (natLit cn) hl)
  let chunk := min chunk 500
  let actTy := mkConst ``BAct
  let mut chunks : Array Expr := #[]
  let mut i := 0
  let mut k := 0
  while i < exprs.size do
    let part := (exprs.extract i (i + chunk)).toList
    let cn := base ++ Name.mkSimple s!"_kb_c{k}"
    let dv : DefinitionVal := { name := cn, levelParams := [], type := mkApp (mkConst ``List [Level.zero]) actTy, value := listExpr actTy part, hints := .abbrev, safety := .safe }
    addDecl (.defnDecl dv)
    chunks := chunks.push (mkConst cn)
    i := i + chunk
    k := k + 1
  let an := base ++ `_kb_acts
  let lty := mkApp (mkConst ``List [Level.zero]) actTy
  let dv : DefinitionVal := { name := an, levelParams := [], type := mkApp (mkConst ``List [Level.zero]) lty, value := listExpr lty chunks.toList, hints := .abbrev, safety := .safe }
  addDecl (.defnDecl dv)
  return (an, exprs.size, rat, tParse)

def litExpr (l : Nat × Bool) : Expr :=
  mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst ``Bool) (natLit l.1)
    (if l.2 then mkConst ``Bool.true else mkConst ``Bool.false)

def cnfDataExpr (F : List (List (Nat × Bool))) : Expr :=
  let litTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst ``Bool)
  let clTy := mkApp (mkConst ``List [Level.zero]) litTy
  listExpr clTy (F.map fun c => listExpr litTy (c.map litExpr))

/-- Kernel check of the certificate against the CNF given as data (computed by compiled code):
measures the checker alone. Not a proof of the original statement. -/
def kbCheckData (n : Name) : MetaM Unit := do
  let v ← valueOf n
  let mut idx := 0
  for e in collectVerify v do
    idx := idx + 1
    let args := e.getAppArgs
    let (E, C) := (args[0]!, args[1]!)
    let bv ← unsafe evalExpr BVLogicalExpr (mkConst ``BVLogicalExpr) E
    let F := toL (Std.Sat.AIG.toCNF bv.bitblast.relabelNat)
    let litTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst ``Bool)
    let fty := mkApp (mkConst ``List [Level.zero]) (mkApp (mkConst ``List [Level.zero]) litTy)
    let fn := n ++ Name.mkSimple s!"_kb_cnfdata_{idx}"
    let dv : DefinitionVal := { name := fn, levelParams := [], type := fty, value := cnfDataExpr F, hints := .abbrev, safety := .safe }
    addDecl (.defnDecl dv)
    let (an, nacts, rat, _) ← defineActs (n ++ Name.mkSimple s!"_d{idx}") E C
    let chk := mkApp2 (mkConst ``LratBits.checkBits) (mkConst fn) (mkConst an)
    let r ← NativeTrust.proveTrueByKernel chk (n ++ Name.mkSimple s!"_kb_checkdata_{idx}") []
      { native := false, trace := true, diagnoseFalse := false }
    logInfo m!"kb {n} #{idx}: {nacts} steps ({rat} RAT); kernel check against the CNF as data \
      (checker alone): {r.ms} ms"

def kbCheck (n : Name) (cnfOnly : Bool) : MetaM Unit := do
  let v ← valueOf n
  let all := collectVerify v
  if all.isEmpty then throwError "kb: no `unsat_of_verifyBVExpr_eq_true` in {n}"
  let mut idx := 0
  for e in all do
    idx := idx + 1
    let args := e.getAppArgs
    let (E, C) := (args[0]!, args[1]!)
    let cnf := mkApp (mkConst ``LratBits.toL) (cnfExpr E)
    if cnfOnly then
      -- reference value by compiled code (untrusted; only used as the expected result)
      let sumE := mkApp (mkConst ``LratBits.cnfSum) cnf
      let bv ← unsafe evalExpr BVLogicalExpr (mkConst ``BVLogicalExpr) E
      let target := cnfSum (toL (Std.Sat.AIG.toCNF bv.bitblast.relabelNat))
      let chk := mkApp2 (mkConst ``Nat.beq) sumE (natLit target)
      let r ← NativeTrust.proveTrueByKernel chk (n ++ Name.mkSimple s!"_kb_cnf_{idx}") []
        { native := false, trace := true, diagnoseFalse := false }
      logInfo m!"kb {n} #{idx}: kernel evaluation of the CNF alone (checksum {target}): {r.ms} ms"
    else
      let (an, nacts, rat, tParse) ← defineActs (n ++ Name.mkSimple s!"_{idx}") E C
      let chk := mkApp2 (mkConst ``LratBits.checkBits) cnf (mkConst an)
      let r ← NativeTrust.proveTrueByKernel chk (n ++ Name.mkSimple s!"_kb_check_{idx}") []
        { native := false, trace := true, diagnoseFalse := false }
      logInfo m!"kb {n} #{idx}: {nacts} steps ({rat} RAT; parsed+converted in {tParse} ms by compiled code); \
        kernel evaluation of the check: {r.ms} ms; copies {r.copies.size}"

elab "kb_check " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  withOptions (Elab.async.set · false) <|
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) (kbCheck n false)

elab "kb_cnf " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  withOptions (Elab.async.set · false) <|
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) (kbCheck n true)

elab "kb_check_data " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  withOptions (Elab.async.set · false) <|
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) (kbCheckData n)


/-- The soundness chain of `Reflect.unsat_of_verifyBVExpr_eq_true`, with the bitmask checker and a
structured certificate in place of the LRAT parser and core's checker. -/
theorem kb_unsat (bv : BVLogicalExpr) (acts : List (List BAct))
    (h : checkBits (toL (KC.Std.Sat.AIG.toCNF
        (@KC.Std.Sat.AIG.Entrypoint.relabelNat BVBit instDecidableEqBVBit
          KC.Std.Tactic.BVDecide.instHashableBVBit
          (KC.Std.Tactic.BVDecide.BVLogicalExpr.bitblast bv)))) acts = true) :
    bv.Unsat :=
  KC.Std.Tactic.BVDecide.BVLogicalExpr.unsat_of_bitblast bv
    ((@KC.Std.Sat.AIG.Entrypoint.relabelNat_unsat_iff BVBit instDecidableEqBVBit
        KC.Std.Tactic.BVDecide.instHashableBVBit
        (KC.Std.Tactic.BVDecide.BVLogicalExpr.bitblast bv)).mp
      ((KC.Std.Sat.AIG.toCNF_equisat _).mp (unsat_of_checkBits _ _ h)))

/-- Prove `E.Unsat` for the certificate `C` with the kernel; returns the proof term
`kb_unsat E acts h` and the timing. -/
def proveUnsat (base : Name) (E C : Expr) : MetaM (Expr × Nat × Nat × Nat) := do
  let (an, nacts, rat, _) ← defineActs base E C
  let cnf := mkApp (mkConst ``LratBits.toL) (cnfExpr E)
  let chk := mkApp2 (mkConst ``LratBits.checkBits) cnf (mkConst an)
  let r ← NativeTrust.proveTrueByKernel chk (base ++ `_kb_check) []
    { native := false, trace := true, diagnoseFalse := false }
  return (mkApp3 (mkConst ``LratBits.kb_unsat) E (mkConst an) (mkConst r.thm), r.ms, nacts, rat)

/-- Replace every `unsat_of_verifyBVExpr_eq_true E C ax` in theorem `n` and add `n.kb` with the same
statement; refuses unless the result uses standard axioms only. -/
def kbKernelize (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let v ← valueOf n
  let all := collectVerify v
  if all.isEmpty then throwError "kb: no `unsat_of_verifyBVExpr_eq_true` in {n}"
  let mut repl : Std.HashMap Expr Expr := {}
  let mut idx := 0
  for e in all do
    if repl.contains e then continue
    idx := idx + 1
    let args := e.getAppArgs
    let (pf, ms, nacts, rat) ← proveUnsat (n ++ Name.mkSimple s!"_kb{idx}") args[0]! args[1]!
    logInfo m!"kb {n} #{idx}: {nacts} steps ({rat} RAT); kernel evaluation of the check: {ms} ms"
    repl := repl.insert e pf
  let v' := v.replace fun e => repl.get? e
  let t0 ← IO.monoMsNow
  addDecl (.thmDecl { name := n ++ `kb, levelParams := ci.levelParams, type := ci.type, value := v' })
  let dt := (← IO.monoMsNow) - t0
  let axs ← collectAxioms (n ++ `kb)
  unless axs.all NativeTrust.stdAxioms.contains do
    throwError "kb: {n ++ `kb} uses non-standard axioms {axs.toList}"
  logInfo m!"kb: added {n ++ `kb} (kernel check of the assembled theorem {dt} ms; axioms {axs.toList})"

elab "kb_kernelize " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  withOptions (Elab.async.set · false) <|
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) (kbKernelize n)

/-- The `bv_decide` axioms of an imported module (private names included), in declaration order. -/
def bvdAxioms (m : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? m | throwError "kb: module {m} is not imported"
  let names := env.header.moduleData[idx.toNat]!.constNames
  return names.filter fun c =>
    (match env.find? c with | some (.axiomInfo _) => true | _ => false) &&
    (c.toString.splitOn "._native.bv_decide.ax_").length > 1

/-- For every `bv_decide` axiom `ax : verifyBVExpr E C = true` of module `m`: prove `E.Unsat` with
the kernel (theorem `kbfact.<i>`), then re-prove every theorem of `m` that uses `ax` (`T.kb`, same
statement, standard axioms), when its proof term is available. -/
def kbModule (m : Name) : MetaM Unit := do
  let env ← getEnv
  let axs ← bvdAxioms m
  let some idx := env.getModuleIdx? m | throwError "kb: module {m} is not imported"
  let thms := (env.header.moduleData[idx.toNat]!.constNames).filter fun c =>
    match env.find? c with | some (.thmInfo _) => true | _ => false
  logInfo m!"kb {m}: {axs.size} bv_decide axioms"
  let mut i := 0
  let mut j := 0
  for ax in axs do
    i := i + 1
    let ty := (← getConstInfo ax).type
    let some (_, lhs, _) := ty.eq? | throwError "kb: unexpected axiom type {ty}"
    unless lhs.isAppOfArity ``Reflect.verifyBVExpr 2 do throwError "kb: unexpected axiom type {ty}"
    let (E, C) := (lhs.getArg! 0, lhs.getArg! 1)
    let base := Name.mkSimple s!"kbfact_{i}"
    -- sizes (compiled code, for the report only)
    let bv ← unsafe evalExpr BVLogicalExpr (mkConst ``BVLogicalExpr) E
    let L := toL (Std.Sat.AIG.toCNF bv.bitblast.relabelNat)
    let maxv := L.foldl (fun a c => c.foldl (fun a l => max a l.1) a) 0
    logInfo m!"kb {ax}: CNF {L.length} clauses, {L.foldl (fun a c => a + c.length) 0} literals, max atom {maxv}; certificate {(← stringOfConst C).length} chars"
    let t0 ← IO.monoMsNow
    let (pf, ms, nacts, rat) ← proveUnsat base E C
    let fact := base ++ `unsat
    addDecl (.thmDecl { name := fact, levelParams := [], type := mkApp (mkConst ``BVLogicalExpr.Unsat) E, value := pf })
    let fax ← collectAxioms fact
    logInfo m!"kb {ax}: {nacts} steps ({rat} RAT); kernel check {ms} ms (total {(← IO.monoMsNow) - t0} ms); \
      {fact} : BVLogicalExpr.Unsat {E}; axioms {fax.toList}"
    -- theorems of `m` whose proof uses `ax` directly
    for t in thms do
      let some (.thmInfo tv) := (← getEnv).find? t | continue
      unless tv.value.getUsedConstants.contains ax do continue
      let v' := tv.value.replace fun e =>
        if e.isAppOfArity ``Reflect.unsat_of_verifyBVExpr_eq_true 3 && e.appArg! == mkConst ax then
          some (mkConst fact) else none
      if v'.getUsedConstants.contains ax then
        logInfo m!"kb {t}: uses {ax} outside `unsat_of_verifyBVExpr_eq_true`; not rebuilt"
        continue
      j := j + 1
      let nm := (Name.mkSimple s!"kbthm_{j}") ++ `kb
      try
        addDecl (.thmDecl { name := nm, levelParams := tv.levelParams, type := tv.type, value := v' })
        let ta ← collectAxioms nm
        let same := ((← getConstInfo nm).type == tv.type)
        logInfo m!"kb {t}: re-proved as {nm} (statement identical: {same}); axioms {ta.toList}"
        unless ta.all NativeTrust.stdAxioms.contains do logInfo m!"kb {nm}: NON-STANDARD AXIOMS"
      catch ex => logInfo m!"kb {t}: rebuilding failed: {ex.toMessageData}"

elab "kb_module " id:ident : command => liftTermElabM do
  let m := id.getId
  withOptions (Elab.async.set · false) <|
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) (kbModule m)

/-- Sizes, by compiled code. -/
elab "#kb_size " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let v ← valueOf n
  for e in collectVerify v do
    let args := e.getAppArgs
    let s ← stringOfConst args[1]!
    let acts ← match LRAT.parseLRATProof s.toUTF8 with
      | .ok a => pure a | .error err => throwError err
    let bv ← unsafe evalExpr BVLogicalExpr (mkConst ``BVLogicalExpr) args[0]!
    let entry := bv.bitblast
    let cnf := Std.Sat.AIG.toCNF entry.relabelNat
    let L := toL cnf
    let nlits := L.foldl (fun a c => a + c.length) 0
    let maxv := L.foldl (fun a c => c.foldl (fun a l => max a l.1) a) 0
    let mut nrup : Nat := 0
    let mut nrat : Nat := 0
    let mut ndel : Nat := 0
    let mut nemp : Nat := 0
    let mut nhints : Nat := 0
    let mut ids : Array Nat := #[]
    for a in acts do
      match a with
      | .addRup id _ h => nrup := nrup + 1; nhints := nhints + h.size; ids := ids.push id
      | .addEmpty id h => nemp := nemp + 1; nhints := nhints + h.size; ids := ids.push id
      | .addRat id _ _ h r => nrat := nrat + 1; nhints := nhints + h.size + r.size; ids := ids.push id
      | .del _ => ndel := ndel + 1
    let consec := (ids.toList.zip (ids.toList.drop 1)).all fun (a, b) => b == a + 1
    let firstId : Nat := ids[0]?.getD 0
    logInfo m!"{n}: AIG {entry.aig.decls.size} nodes; CNF {L.length} clauses, {nlits} literals, max atom {maxv}; \
      LRAT {acts.size} actions (rup {nrup}, empty {nemp}, rat {nrat}, del {ndel}), {nhints} hints, \
      first id {firstId}, ids consecutive {consec}; cert {s.length} chars"

end LratBits
