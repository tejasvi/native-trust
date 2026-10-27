module

public import BVS.Driver.Select
public meta import BVS.Driver.Select

public meta section
/-!
# Facts from several modules, converted together

`bvs5_group "M₁:i,j,…" "M₂:k,…" …` converts the selected `bv_decide` axioms of the modules `M₁, M₂, …`
(indices as in `bvs5_list`) in one process (`BVS.Driver4.proveUnsat`, theorems `bvsg_<M>_<i>.unsat`, with the
dots of `M` replaced by `_`), then rebuilds, in dependency order, every declaration of these modules whose value
depends on a converted axiom, directly or through another declaration of these modules. A rebuilt declaration
refers to the rebuilt versions of the declarations it uses, also across modules (names `bvsg_<k>`, original
types). This is needed when a theorem uses facts from several modules or packages: converting each module
separately leaves its rebuilt declarations referring to the original theorems of the other modules, which still
depend on their native axioms.

Output lines as in `BVS.Driver.Select` (`BVS_STATS`, `BVS_UNSAT`, `BVS_USER`, `BVS_DONE` on stderr). All proofs
are checked by the kernel; this file only builds terms.
-/
open Lean Meta Elab Command Std.Tactic.BVDecide

namespace BVSGroup
open BVS.Driver5 (emit oneLine bvdAxioms moduleConsts axiomE kindOf stdAxioms)

/-- `BVS.Driver5.rebuildUsers` over several modules, with one map of rebuilt declarations. -/
def rebuildMulti (mods : Array Name) (conv : NameMap Name) (bvdSet : NameSet) (pfx : String) :
    MetaM (Nat × Nat × Nat × Nat) := do
  let mut consts : Array Name := #[]
  for m in mods do consts := consts ++ (← moduleConsts m)
  let env ← getEnv
  let valOf (c : Name) : Option (Expr × Bool) := match env.find? c with
    | some (.thmInfo t) => some (t.value, true)
    | some (.defnInfo d) => if d.safety == DefinitionSafety.safe then some (d.value, false) else none
    | _ => none
  let inMods : NameSet := consts.foldl (fun s c => s.insert c) {}
  let mut deps : NameMap (Array Name) := {}
  for c in consts do
    if let some (v, _) := valOf c then
      deps := deps.insert c (v.getUsedConstants.filter fun d => inMods.contains d || conv.contains d)
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
        addDecl (.defnDecl { name := nm, levelParams := ci.levelParams, type := ci.type, value := v',
                             hints := d.hints, safety := .safe })
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

def parseItem (s : String) : Name × List Nat :=
  match s.splitOn ":" with
  | [m, is] => (m.toName, (is.splitOn ",").filterMap String.toNat?)
  | _ => (s.toName, [])

elab "bvs5_group " items:str+ : command => liftTermElabM do
  withOptions (Elab.async.set · false) <|
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let mut mods : Array Name := #[]
  let mut conv : NameMap Name := {}
  let mut bvdSet : NameSet := {}
  let mut allOk := true
  let mut nfacts := 0
  for it in items do
    let (m, idxs) := parseItem it.getString
    mods := mods.push m
    let axs ← bvdAxioms m
    bvdSet := axs.foldl (fun s a => s.insert a) bvdSet
    for i in idxs do
      unless i < axs.size do throwError "bvs5_group: no index {i} ({m} has {axs.size} bv_decide axioms)"
      nfacts := nfacts + 1
      let ax := axs[i]!
      let E ← axiomE ax
      let base := Name.mkSimple s!"bvsg_{m.toString.replace "." "_"}_{i}"
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
  let (k, nStd, nLeft, nFail) ← rebuildMulti mods conv bvdSet "bvsg"
  emit s!"BVS_DONE\t{mods.toList}\tfacts={nfacts}\tconverted={conv.size}\tall_unsat_ok={allOk}\tusers={k}\tusers_std={nStd}\tusers_axiom_left={nLeft}\tusers_failed={nFail}"

end BVSGroup
