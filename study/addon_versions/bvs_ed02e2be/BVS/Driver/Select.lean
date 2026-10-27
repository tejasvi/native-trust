import BVS.Driver.Core
/-!
# Selected facts of a module: sharded or single-process conversion

The sharding commands of `BVS.Driver.Core` (`bvs4_prep_module` / `bvs4_chunk` / `bvs4_assemble_module`)
convert every `bv_decide` axiom of a module. The commands here take the facts by index: the position
among the module's `._native.bv_decide.ax_` axioms, from `0` (`bvs5_list M` prints them).

* `bvs5_prep M "dir" k i₁ i₂ …` (in a module `P`): for each selected axiom, runs the untrusted pipeline
  and proves the base check and the empty clause (`BVS.Driver4.prepFact`), deals the LRAT chunks
  round-robin into `k` shard files `dir/<P>_S<r>.lean` (each `import P` and `bvs4_chunk …` lines), and
  writes `dir/<P>_Final.lean` (imports the shards, `bvs5_assemble M i₁ i₂ …`).
* `bvs5_assemble M i₁ i₂ …`: `bvs5fact_<i>.unsat : BVLogicalExpr.Unsat E` from the chunk theorems
  (`BVS.Driver4.assembleFact`), then every declaration of `M` whose value depends on the converted
  axioms (directly or through other declarations of `M`) is re-added as `bvs5_<k>` with the same type,
  in dependency order.
* `bvs5_fact M i₁ i₂ …`: the same conversion in one process, without shards.

Progress lines go to stderr: `BVS_UNSAT` per fact, `BVS_USER` per rebuilt declaration (original name,
new name, kind, whether the type is identical, whether only standard axioms are used), `BVS_DONE`.
All proofs are checked by the kernel; compiled code only produces data and terms.
-/
open Lean Meta Elab Command Std.Tactic.BVDecide

namespace BVS.Driver5

def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def emit (s : String) : IO Unit := do
  let e ← IO.getStderr
  e.putStrLn s
  e.flush

def oneLine (s : String) : String :=
  let s := s.replace "\n" " "
  let s := s.replace "\t" " "
  if s.length > 400 then String.join ((s.toList.take 400).map Char.toString) ++ "…" else s

/-- The `bv_decide` axioms of an imported module, in declaration order. -/
def bvdAxioms (m : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? m | throwError "bvs5: module {m} is not imported"
  let names := env.header.moduleData[idx.toNat]!.constNames
  return names.filter fun c =>
    (match env.find? c with | some (.axiomInfo _) => true | _ => false) &&
    (c.toString.splitOn "._native.bv_decide.ax_").length > 1

def moduleConsts (m : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? m | throwError "bvs5: module {m} is not imported"
  return env.header.moduleData[idx.toNat]!.constNames

/-- The problem `E` of an axiom `ax : verifyBVExpr E C = true`. -/
def axiomE (ax : Name) : MetaM Expr := do
  let ty := (← getConstInfo ax).type
  let some (_, lhs, _) := ty.eq? | throwError "bvs5: unexpected axiom type {ty}"
  unless lhs.isAppOfArity ``Reflect.verifyBVExpr 2 do throwError "bvs5: unexpected axiom type {ty}"
  return lhs.getArg! 0

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | _ => "other"

/-- Re-add every declaration of `m` whose value depends on the axioms in `conv` (axiom ↦ theorem of
`E.Unsat`), with `unsat_of_verifyBVExpr_eq_true E C ax` replaced by the theorem, as `<pfx>_<k>`. -/
def rebuildUsers (m : Name) (conv : NameMap Name) (bvdSet : NameSet) (pfx : String) : MetaM (Nat × Nat × Nat × Nat) := do
  let consts ← moduleConsts m
  let env ← getEnv
  let valOf (c : Name) : Option (Expr × Bool) := match env.find? c with
    | some (.thmInfo t) => some (t.value, true)
    | some (.defnInfo d) => if d.safety == DefinitionSafety.safe then some (d.value, false) else none
    | _ => none
  let inMod : NameSet := consts.foldl (fun s c => s.insert c) {}
  let mut deps : NameMap (Array Name) := {}
  for c in consts do
    if let some (v, _) := valOf c then
      deps := deps.insert c (v.getUsedConstants.filter fun d => inMod.contains d || conv.contains d)
  let mut affected : NameSet := {}
  let mut changed := true
  while changed do
    changed := false
    for c in consts do
      if affected.contains c then continue
      let some ds := deps.find? c | continue
      if ds.any (fun d => conv.contains d || affected.contains d) then
        affected := affected.insert c
        changed := true
  let mut order : Array Name := #[]
  let mut visited : NameSet := {}
  for r in consts do
    if !affected.contains r || visited.contains r then continue
    visited := visited.insert r
    let mut stack : Array (Name × Nat) := #[(r, 0)]
    while h : stack.size > 0 do
      let (c, i) := stack.back
      let ds := ((deps.find? c).getD #[]).filter affected.contains
      if i < ds.size then
        stack := stack.set! (stack.size - 1) (c, i + 1)
        let d := ds[i]!
        unless visited.contains d do
          visited := visited.insert d
          stack := stack.push (d, 0)
      else
        stack := stack.pop
        order := order.push c
  let mut rebuilt : NameMap Name := {}
  let mut k := 0
  let mut nStd := 0
  let mut nLeft := 0
  let mut nFail := 0
  for c in order do
    let some ci := env.find? c | continue
    let some (v, isThm) := valOf c | continue
    let v' := v.replace fun e =>
      if e.isAppOfArity ``Reflect.unsat_of_verifyBVExpr_eq_true 3 then
        match e.appArg! with
        | .const a _ => (conv.find? a).map mkConst
        | _ => none
      else match e with
        | .const d ls => (rebuilt.find? d).map (mkConst · ls)
        | _ => none
    if v'.getUsedConstants.any conv.contains then
      emit s!"BVS_USER_SKIP\t{c}\tuses a converted axiom outside `unsat_of_verifyBVExpr_eq_true`"
      nFail := nFail + 1
      continue
    k := k + 1
    let nm := Name.mkSimple s!"{pfx}_{k}"
    let t0 ← IO.monoMsNow
    try
      if isThm then
        addDecl (.thmDecl { name := nm, levelParams := ci.levelParams, type := ci.type, value := v' })
      else
        let .defnInfo d := ci | unreachable!
        let dv : DefinitionVal := { name := nm, levelParams := ci.levelParams, type := ci.type, value := v',
                                    hints := d.hints, safety := .safe }
        addDecl (.defnDecl dv)
      let dt := (← IO.monoMsNow) - t0
      let axs' ← collectAxioms nm
      let std := axs'.all stdAxioms.contains
      let same := (← getConstInfo nm).type == ci.type
      let otherBvd := (axs'.filter bvdSet.contains).size
      let convLeft := (axs'.filter conv.contains).size
      rebuilt := rebuilt.insert c nm
      if std && same then nStd := nStd + 1
      if convLeft > 0 || !same then nLeft := nLeft + 1
      emit s!"BVS_USER\t{c}\t{nm}\t{kindOf ci}\tsame_type={same}\tstd={std}\tother_bvd={otherBvd}\tconv_left={convLeft}\tkernel_ms={dt}\t{axs'.toList}"
    catch ex =>
      nFail := nFail + 1
      emit s!"BVS_USER_FAIL\t{c}\t{nm}\t{oneLine (← ex.toMessageData.toString)}"
  return (k, nStd, nLeft, nFail)

def factBase (i : Nat) : Name := Name.mkSimple s!"bvs5fact_{i}"

/-- Write the shard files and the final file for the chunk tables of the prepared facts. -/
def writeShardFiles (m : Name) (idxs : Array Nat) (tables : Array (Name × Array (Nat × Nat))) (d : String)
    (k : Nat) : MetaM Unit := do
  let me := (← getEnv).mainModule
  let mut jobs : Array (Array (Name × Nat)) := Array.replicate k #[]
  let mut r := 0
  for (base, table) in tables do
    for j in [0:table.size] do
      jobs := jobs.modify r (·.push (base, j))
      r := (r + 1) % k
  let pre := me.toString
  for q in [0:k] do
    let lines := jobs[q]!.toList.map fun (b, j) => s!"bvs4_chunk {b} {j}"
    IO.FS.writeFile s!"{d}/{pre}_S{q}.lean" (String.intercalate "\n"
      ([s!"import {pre}", "set_option maxHeartbeats 0", "set_option maxRecDepth 1000000",
        "set_option Elab.async false", s!"set_option bvs4.log \"{d}/{pre}_S{q}.progress\""] ++ lines) ++ "\n")
  IO.FS.writeFile s!"{d}/{pre}_Final.lean" (String.intercalate "\n"
    ((List.range k).map (fun q => s!"import {pre}_S{q}") ++
      ["set_option maxHeartbeats 0", "set_option maxRecDepth 1000000", "set_option Elab.async false",
       s!"bvs5_assemble {m} {String.intercalate " " (idxs.toList.map toString)}"]) ++ "\n")

elab "bvs5_prep " id:ident dir:str k:num ns:num+ : command => liftTermElabM do
  withOptions (Elab.async.set · false) <|
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let m := id.getId
  let axs ← bvdAxioms m
  let idxs := ns.map (·.getNat)
  let mut tables : Array (Name × Array (Nat × Nat)) := #[]
  for i in idxs do
    unless i < axs.size do throwError "bvs5: no index {i} ({m} has {axs.size} bv_decide axioms)"
    let ax := axs[i]!
    let E ← axiomE ax
    let base := factBase i
    emit s!"BVS_PREP\t{m}\t{i}\t{ax}"
    let t0 ← IO.monoMsNow
    let table ← BVS.Driver4.prepFact base E
    emit s!"BVS_PREP_DONE\t{m}\t{i}\tchunks={table.size}\tms={(← IO.monoMsNow) - t0}"
    tables := tables.push (base, table)
  writeShardFiles m idxs tables dir.getString (max 1 k.getNat)
  logInfo m!"bvs5: {idxs.size} facts prepared; shard files and the final file written to {dir.getString}"

elab "bvs5_assemble " id:ident ns:num+ : command => liftTermElabM do
  withOptions (Elab.async.set · false) <|
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let m := id.getId
  let axs ← bvdAxioms m
  let bvdSet : NameSet := axs.foldl (fun s a => s.insert a) {}
  let idxs := ns.map (·.getNat)
  let mut conv : NameMap Name := {}
  let mut allOk := true
  for i in idxs do
    unless i < axs.size do throwError "bvs5: no index {i} ({m} has {axs.size} bv_decide axioms)"
    let ax := axs[i]!
    let E ← axiomE ax
    let base := factBase i
    let t0 ← IO.monoMsNow
    try
      let pf ← BVS.Driver4.assembleFact base E
      let fact := base ++ `unsat
      addDecl (.thmDecl { name := fact, levelParams := [], type := mkApp (mkConst ``BVLogicalExpr.Unsat) E, value := pf })
      let fax ← collectAxioms fact
      let std := fax.all stdAxioms.contains
      emit s!"BVS_UNSAT\t{m}\t{i}\t{ax}\t-\t0\t-\t{(← IO.monoMsNow) - t0}\t{fact}\t{std}\t{fax.toList}"
      if std then conv := conv.insert ax fact else allOk := false
    catch ex =>
      allOk := false
      emit s!"BVS_UNSAT_FAIL\t{m}\t{i}\t{ax}\t{(← IO.monoMsNow) - t0}\t{oneLine (← ex.toMessageData.toString)}"
  if conv.isEmpty then
    emit s!"BVS_DONE\t{m}\t{idxs.toList}\tconverted=0"
    return
  let (k, nStd, nLeft, nFail) ← rebuildUsers m conv bvdSet "bvs5"
  emit s!"BVS_DONE\t{m}\t{idxs.toList}\tconverted={conv.size}\tall_unsat_ok={allOk}\tusers={k}\tusers_std={nStd}\tusers_axiom_left={nLeft}\tusers_failed={nFail}"

/-- `bvs5_fact M i₁ i₂ …`: the single-process conversion (`BVS.Driver4.proveUnsat`: data, base check and chunks
in this module) of the `bv_decide` axioms of `M` with these indices, then the users (as `bvs5_assemble`). -/
elab "bvs5_fact " id:ident ns:num+ : command => liftTermElabM do
  withOptions (Elab.async.set · false) <|
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let m := id.getId
  let axs ← bvdAxioms m
  let bvdSet : NameSet := axs.foldl (fun s a => s.insert a) {}
  let idxs := ns.map (·.getNat)
  let mut conv : NameMap Name := {}
  let mut allOk := true
  for i in idxs do
    unless i < axs.size do throwError "bvs5: no index {i} ({m} has {axs.size} bv_decide axioms)"
    let ax := axs[i]!
    let E ← axiomE ax
    let base := factBase i
    let t0 ← IO.monoMsNow
    try
      let (pf, st) ← BVS.Driver4.proveUnsat base E
      let fact := base ++ `unsat
      addDecl (.thmDecl { name := fact, levelParams := [], type := mkApp (mkConst ``BVLogicalExpr.Unsat) E, value := pf })
      let fax ← collectAxioms fact
      let std := fax.all stdAxioms.contains
      emit s!"BVS_STATS\t{m}\t{i}\tnodes={st.nodes}\tclauses={st.clauses}\tsteps={st.steps}\thints={st.hints}\tchunks={st.chunks}\tbase_ms={st.baseMs}\tchunk_ms={st.chunkMs}"
      emit s!"BVS_UNSAT\t{m}\t{i}\t{ax}\t{st.steps}\t0\t{st.baseMs + st.chunkMs}\t{(← IO.monoMsNow) - t0}\t{fact}\t{std}\t{fax.toList}"
      if std then conv := conv.insert ax fact else allOk := false
    catch ex =>
      allOk := false
      emit s!"BVS_UNSAT_FAIL\t{m}\t{i}\t{ax}\t{(← IO.monoMsNow) - t0}\t{oneLine (← ex.toMessageData.toString)}"
  if conv.isEmpty then
    emit s!"BVS_DONE\t{m}\t{idxs.toList}\tconverted=0"
    return
  let (k, nStd, nLeft, nFail) ← rebuildUsers m conv bvdSet "bvs5"
  emit s!"BVS_DONE\t{m}\t{idxs.toList}\tconverted={conv.size}\tall_unsat_ok={allOk}\tusers={k}\tusers_std={nStd}\tusers_axiom_left={nLeft}\tusers_failed={nFail}"

/-- `bvs5_list M`: the indices and names of the `bv_decide` axioms of the imported module `M`. -/
elab "bvs5_list " id:ident : command => liftTermElabM do
  let axs ← bvdAxioms id.getId
  for i in [0:axs.size] do
    logInfo m!"{i}: {axs[i]!}"

end BVS.Driver5
