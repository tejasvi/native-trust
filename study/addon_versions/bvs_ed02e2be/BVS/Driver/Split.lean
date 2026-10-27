import BVS.SplitBase
import BVS.Driver.Select
/-!
# Split base check: sharded conversion with `bvs_unsat5`

For a `bv_decide` axiom `ax : verifyBVExpr E C = true` of a module `M` (index `i` as in
`BVS.Driver.Select`):

* `bvs6_prep M "dir" k S i` (in a module `P`; compiled code, untrusted): bit-blasts `E`, solves and
  prepares the certificate, and cuts the entry list into segments of `S` nodes (segment `j`: nodes
  `1 + (j-1)·S …`, newest entry first). Defines the clause tree, the hint chunks, the segments
  (`_bvs_seg<j>`) and the tables (`_bvs_meta`, `_bvs_dims`, `_bvs_seginfo`), proves the empty-clause
  test, and writes `k` shard files and the final file to `dir`.
* shards: `bvs6_blast M i` proves `blastCk E (seg_m ++ (… ++ (seg_1 ++ []))) n out = true` (the
  bit-blaster's run, one declaration); `bvs6_seg base j` proves `segOK` for segment `j`; `bvs4_chunk`
  the LRAT chunks.
* `bvs6_assemble M i`: folds the segments with `acc_step`, chains the chunks, applies `bvs_unsat5`
  (theorem `bvs6fact_<i>.unsat : E.Unsat`), and re-adds the users of the axiom as `bvs6_<k>` with
  their original types (as in `BVS.Driver.Select`).
-/
open Lean Meta Elab Command Std.Tactic.BVDecide

namespace BVS.Driver6
open BVS.Driver4 (logLine addDefn addTrueThm listE natTy ltTy treeE hintsE stepsTy hintsTy solve prepare
  readMeta listLit natLitOf)

def entTy : Expr := mkConst ``BVS.Ent
def entE : Ent → Expr
  | .gate k l r => mkApp3 (mkConst ``Ent.gate) (mkRawNatLit k) (mkRawNatLit l) (mkRawNatLit r)
  | .atom k v i => mkApp3 (mkConst ``Ent.atom) (mkRawNatLit k) (mkRawNatLit v) (mkRawNatLit i)
def esTy : Expr := mkApp (mkConst ``List [0]) entTy
def trueE : Expr := mkConst ``Bool.true
def boolTrueThm (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e trueE
def reflTrue : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) trueE

def nSeg (base : Name) (j : Nat) : Name := base ++ Name.mkSimple s!"_bvs_seg{j}"
def nSegOk (base : Name) (j : Nat) : Name := base ++ Name.mkSimple s!"_bvs_g{j}"

/-- `seg_j ++ (… ++ (seg_1 ++ []))`. -/
def esAfter (base : Name) : Nat → Expr
  | 0 => mkApp (mkConst ``List.nil [0]) entTy
  | j + 1 => mkApp3 (mkConst ``List.append [0]) entTy (mkConst (nSeg base (j + 1))) (esAfter base j)

def nGates (seg : List Ent) : Nat := seg.foldl (fun a e => match e with | .gate .. => a + 1 | .atom .. => a) 0

structure SegInfo where
  m : Nat
  n : Nat
  out : Nat
  lenG : Nat
  /-- per segment `j` (index `j - 1`): bound, bound of the older segments, first key, number of leaves -/
  segs : Array (Nat × Nat × Nat × Nat)

def readSegInfo (base : Name) : MetaM SegInfo := do
  let some v := (← getConstInfo (base ++ `_bvs_seginfo)).value? | throwError "bvs6: no segment table"
  let xs ← (← listLit v).mapM natLitOf
  let m :: n :: out :: lenG :: rest := xs | throwError "bvs6: bad segment table"
  let rest := rest.toArray
  unless rest.size == 4 * m do throwError "bvs6: bad segment table"
  let segs := (List.range m).toArray.map fun j => (rest[4 * j]!, rest[4 * j + 1]!, rest[4 * j + 2]!, rest[4 * j + 3]!)
  return { m, n, out, lenG, segs }

def addThmTimed (n : Name) (ty pf : Expr) : CoreM Nat := do
  let t0 ← IO.monoMsNow
  withOptions (fun o => o.set `Elab.async false) <|
    addDecl (.thmDecl { name := n, levelParams := [], type := ty, value := pf })
  return (← IO.monoMsNow) - t0

/-! ## Phase A -/

/-- Phase A for one fact: returns the chunk table and the number of segments. -/
def prepFact6 (base : Name) (E : Expr) (S : Nat) : MetaM (Array (Nat × Nat) × Nat) := do
  let opts ← getOptions
  let chunk := max 1 (BVS.Driver4.bvs4.chunk.get opts)
  let S := max 1 S
  let bv ← unsafe evalExpr BVLogicalExpr (mkConst ``BVLogicalExpr) E
  unless supportedBool bv do throwError "bvs6: unsupported constructors in {toString bv |>.take 300}"
  let (bst, out) := blastBool St.empty bv
  let F := (cnfOf bst.es out).toArray
  logLine s!"{base}: {bst.n} nodes, CNF {F.size} clauses"
  let tag := s!"{base.toString.replace "." "_"}_{← IO.monoNanosNow}"
  let t1 ← IO.monoMsNow
  let proof ← solve F tag (BVS.Driver4.bvs4.timeout.get opts)
  let acts ← match LRAT.parseLRATProof proof with
    | .ok a => pure a
    | .error e => throwError "bvs6: LRAT parse error {e}"
  let prep ← match prepare F acts with
    | .ok p => pure p
    | .error e => throwError "bvs6: {e}"
  let L := F.size
  let N := L + prep.learned.size
  let mut mp : Std.HashMap Nat Leaf := {}
  let lv := (leavesOf bst.es out).toArray
  for i in [0:L] do mp := mp.insert (i + 1) lv[i]!
  for i in [0:prep.learned.size] do mp := mp.insert (L + 1 + i) (.cl prep.learned[i]!)
  let D := Nat.log2 (N + 1) + (if 2 ^ Nat.log2 (N + 1) < N + 1 then 1 else 0)
  let H := 2 ^ D / 2
  addDefn (base ++ `_bvs_T) ltTy (treeE mp N D)
  let mut table : Array (Nat × Nat) := #[]
  let maxH := max 1 (BVS.Driver4.bvs4.chunkHints.get opts)
  let mut i := 0
  let mut k := 0
  while i < prep.hints.size do
    let mut j := i
    let mut h := 0
    while j < prep.hints.size && j - i < chunk && (j == i || h + prep.hints[j]!.length ≤ maxH) do
      h := h + prep.hints[j]!.length
      j := j + 1
    let part := (prep.hints.extract i j).toList
    addDefn (base ++ Name.mkSimple s!"_bvs_s{k}") stepsTy (listE hintsTy (part.map hintsE))
    table := table.push (L + 1 + i, part.length)
    i := j
    k := k + 1
  let nh := prep.hints.foldl (fun a h => a + h.length) 0
  logLine s!"{base}: {prep.learned.size} steps, {nh} hints, {table.size} chunks; solve+prep {(← IO.monoMsNow) - t1} ms"
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) natTy natTy
  addDefn (base ++ `_bvs_meta) (mkApp (mkConst ``List [0]) pairTy)
    (listE pairTy (table.toList.map fun (a, b) => mkApp4 (mkConst ``Prod.mk [0, 0]) natTy natTy (mkRawNatLit a) (mkRawNatLit b)))
  addDefn (base ++ `_bvs_dims) (mkApp (mkConst ``List [0]) natTy) (listE natTy ([D, H, L, N].map mkRawNatLit))
  -- segments: segment `j` holds nodes `1 + (j-1)·S … min(1 + j·S, n) - 1`, newest first
  let n := bst.n
  let m := (n - 1 + S - 1) / S
  let mut info : Array Nat := #[]
  let mut lo := 3
  for j in [1:m + 1] do
    let b := min (1 + j * S) n
    let bprev := 1 + (j - 1) * S
    let seg := (bst.es.drop (n - b)).take (b - bprev)
    unless seg.length == b - bprev do throwError "bvs6: segment {j} has {seg.length} entries, expected {b - bprev}"
    addDefn (nSeg base j) esTy (listE entTy (seg.map entE))
    let len := 3 * nGates seg
    info := info ++ #[b, bprev, lo, len]
    lo := lo + len
  let lenG := lo - 3
  unless lenG + 2 == L do throwError "bvs6: {lenG} gate leaves and 2, but {L} clauses"
  addDefn (base ++ `_bvs_seginfo) (mkApp (mkConst ``List [0]) natTy)
    (listE natTy (([m, n, out, lenG] ++ info.toList).map mkRawNatLit))
  logLine s!"{base}: {m} segments of {S} nodes"
  let T := mkConst (base ++ `_bvs_T)
  let _ ← addTrueThm (base ++ `_bvs_empty) (mkApp4 (mkConst ``BVS.stepEmpty4) T (mkRawNatLit D) (mkRawNatLit H) (mkRawNatLit N))
  return (table, m)

/-! ## Phase B -/

def factE (m : Name) (i : Nat) : MetaM Expr := do
  let axs ← BVS.Driver5.bvdAxioms m
  unless i < axs.size do throwError "bvs6: no index {i} ({m} has {axs.size} bv_decide axioms)"
  BVS.Driver5.axiomE axs[i]!

def factBase (i : Nat) : Name := Name.mkSimple s!"bvs6fact_{i}"

def blastStmt (base : Name) (E : Expr) (si : SegInfo) : Expr :=
  boolTrueThm (mkApp4 (mkConst ``BVS.blastCk) E (esAfter base si.m) (mkRawNatLit si.n) (mkRawNatLit si.out))

def segStmt (base : Name) (D : Nat) (si : SegInfo) (j : Nat) : Expr :=
  let (b, bprev, lo, len) := si.segs[j - 1]!
  boolTrueThm (mkAppN (mkConst ``BVS.segOK) #[mkConst (base ++ `_bvs_T), mkRawNatLit D, mkRawNatLit lo,
    mkConst (nSeg base j), mkRawNatLit b, mkRawNatLit bprev, mkRawNatLit len])

/-! ## Phase C -/

def assembleFact6 (base : Name) (E : Expr) : MetaM Expr := do
  let (tbl, D, H, L, N) ← readMeta base
  let si ← readSegInfo base
  let T := mkConst (base ++ `_bvs_T)
  let lit := mkRawNatLit
  let mut acc := mkApp3 (mkConst ``BVS.entsOK_nil) T (lit H) (lit 1)
  let mut lenR := 0
  for j in [1:si.m + 1] do
    let (b, bprev, lo, len) := si.segs[j - 1]!
    acc := mkAppN (mkConst ``BVS.acc_step) #[T, lit D, lit H, reflTrue, mkConst (nSeg base j), esAfter base (j - 1),
      lit b, lit bprev, lit lenR, lit len, lit lo, reflTrue, acc, mkConst (nSegOk base j)]
    lenR := lenR + len
  unless lenR == si.lenG do throwError "bvs6: leaf count mismatch"
  let lookE := mkApp2 (mkConst ``BVS.look4) T (lit H)
  let mut chain : Option Expr := none
  let mut cur := L + 1
  for j in [0:tbl.size] do
    let (s, cnt) := tbl[j]!
    let c := mkApp4 (mkConst ``BVS.chkUR_sound) lookE (mkConst (base ++ Name.mkSimple s!"_bvs_s{j}"))
      (lit s) (mkConst (base ++ Name.mkSimple s!"_bvs_s{j}_ok"))
    let e := s + cnt
    chain := some <| match chain with
      | none => c
      | some ch => mkApp6 (mkConst ``BVS.ChainL.trans) lookE (lit (L + 1)) (lit cur) (lit e) ch c
    cur := e
  let some ch := chain | throwError "bvs6: no steps"
  return mkAppN (mkConst ``BVS.bvs_unsat5) #[E, T, lit D, lit H, lit L, lit N, lit si.n, lit si.out, lit si.lenG,
    esAfter base si.m, mkConst (base ++ `_bvs_blast), reflTrue, acc, reflTrue, reflTrue, ch, mkConst (base ++ `_bvs_empty)]

/-! ## Commands -/

def writeShardFiles6 (m : Name) (i : Nat) (jobs : Array String) (d : String) (k : Nat) : MetaM Unit := do
  let pre := (← getEnv).mainModule.toString
  let mut per : Array (Array String) := Array.replicate k #[]
  let mut r := 0
  for line in jobs do
    per := per.modify r (·.push line)
    r := (r + 1) % k
  for q in [0:k] do
    IO.FS.writeFile s!"{d}/{pre}_S{q}.lean" (String.intercalate "\n"
      ([s!"import {pre}", "set_option maxHeartbeats 0", "set_option maxRecDepth 1000000",
        "set_option Elab.async false", s!"set_option bvs4.log \"{d}/{pre}_S{q}.progress\""] ++ per[q]!.toList) ++ "\n")
  IO.FS.writeFile s!"{d}/{pre}_Final.lean" (String.intercalate "\n"
    ((List.range k).map (fun q => s!"import {pre}_S{q}") ++
      ["set_option maxHeartbeats 0", "set_option maxRecDepth 1000000", "set_option Elab.async false",
       s!"set_option bvs4.log \"{d}/{pre}_Final.progress\"", s!"bvs6_assemble {m} {i}"]) ++ "\n")

elab "bvs6_prep " id:ident dir:str k:num S:num i:num : command => liftTermElabM do
  withOptions (Elab.async.set · false) <|
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let m := id.getId
  let i := i.getNat
  let axs ← BVS.Driver5.bvdAxioms m
  unless i < axs.size do throwError "bvs6: no index {i} ({m} has {axs.size} bv_decide axioms)"
  let ax := axs[i]!
  let E ← BVS.Driver5.axiomE ax
  let base := factBase i
  BVS.Driver5.emit s!"BVS_PREP\t{m}\t{i}\t{ax}"
  let t0 ← IO.monoMsNow
  let (table, nseg) ← prepFact6 base E S.getNat
  BVS.Driver5.emit s!"BVS_PREP_DONE\t{m}\t{i}\tsegments={nseg}\tchunks={table.size}\tms={(← IO.monoMsNow) - t0}"
  -- the bit-blaster run first (the largest job), then the segments, then the chunks
  let jobs := #[s!"bvs6_blast {m} {i}"] ++ ((List.range nseg).toArray.map fun j => s!"bvs6_seg {base} {j + 1}") ++
    ((List.range table.size).toArray.map fun j => s!"bvs4_chunk {base} {j}")
  writeShardFiles6 m i jobs dir.getString (max 1 k.getNat)
  logInfo m!"bvs6: prepared; shard files and the final file written to {dir.getString}"

elab "bvs6_blast " id:ident i:num : command => liftTermElabM do
  withOptions (Elab.async.set · false) <|
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let i := i.getNat
  let base := factBase i
  let E ← factE id.getId i
  let si ← readSegInfo base
  let ms ← addThmTimed (base ++ `_bvs_blast) (blastStmt base E si) reflTrue
  logLine s!"{base}: bit-blaster run ({si.n} nodes, {si.m} segments) {ms} ms"

elab "bvs6_seg " id:ident j:num : command => liftTermElabM do
  withOptions (Elab.async.set · false) <|
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let base := id.getId
  let j := j.getNat
  let (_, D, _, _, _) ← readMeta base
  let si ← readSegInfo base
  let ms ← addThmTimed (nSegOk base j) (segStmt base D si j) reflTrue
  logLine s!"{base}: segment {j} ({si.segs[j - 1]!.2.2.2} leaves) {ms} ms"

elab "bvs6_assemble " id:ident ns:num+ : command => liftTermElabM do
  withOptions (Elab.async.set · false) <|
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let m := id.getId
  let axs ← BVS.Driver5.bvdAxioms m
  let bvdSet : NameSet := axs.foldl (fun s a => s.insert a) {}
  let idxs := ns.map (·.getNat)
  let mut conv : NameMap Name := {}
  let mut allOk := true
  for i in idxs do
    let ax := axs[i]!
    let base := factBase i
    let t0 ← IO.monoMsNow
    try
      let E ← BVS.Driver5.axiomE ax
      let pf ← assembleFact6 base E
      let fact := base ++ `unsat
      addDecl (.thmDecl { name := fact, levelParams := [], type := mkApp (mkConst ``BVLogicalExpr.Unsat) E, value := pf })
      let fax ← collectAxioms fact
      let std := fax.all BVS.Driver5.stdAxioms.contains
      BVS.Driver5.emit s!"BVS_UNSAT\t{m}\t{i}\t{ax}\t-\t0\t-\t{(← IO.monoMsNow) - t0}\t{fact}\t{std}\t{fax.toList}"
      logLine s!"{base}: assembled in {(← IO.monoMsNow) - t0} ms"
      if std then conv := conv.insert ax fact else allOk := false
    catch ex =>
      allOk := false
      BVS.Driver5.emit s!"BVS_UNSAT_FAIL\t{m}\t{i}\t{ax}\t{(← IO.monoMsNow) - t0}\t{BVS.Driver5.oneLine (← ex.toMessageData.toString)}"
  if conv.isEmpty then
    BVS.Driver5.emit s!"BVS_DONE\t{m}\t{idxs.toList}\tconverted=0"
    return
  let (k, nStd, nLeft, nFail) ← BVS.Driver5.rebuildUsers m conv bvdSet "bvs6"
  BVS.Driver5.emit s!"BVS_DONE\t{m}\t{idxs.toList}\tconverted={conv.size}\tall_unsat_ok={allOk}\tusers={k}\tusers_std={nStd}\tusers_axiom_left={nLeft}\tusers_failed={nFail}"

end BVS.Driver6
