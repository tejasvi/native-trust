import BVS.Unsat
import Lean
/-!
# Driver: re-prove `bv_decide` facts with the kernel-checked pipeline

For a `bv_decide` proof `Reflect.unsat_of_verifyBVExpr_eq_true E C ax` (or a module axiom
`ax : verifyBVExpr E C = true`), compiled code (untrusted):
1. runs `BVS.blastBool` on `E` and writes the CNF `cnfOf` as DIMACS;
2. calls CaDiCaL for an LRAT proof, keeps the steps that reach the empty clause, renumbers them, and
   annotates every hint with the variable it makes unit;
3. defines the leaf tree `T` (gate descriptors for the original clauses, then the learned clauses)
   and the hint lists, in chunks.

The kernel then checks `check4 E T D H L` (one declaration: bit-blasting, well-formedness, `T` holds
the CNF), each chunk of steps with `chkUR` (one declaration per chunk) and the empty clause, and the
pieces are assembled with `BVS.bvs_unsat4` into a proof of `E.Unsat`.

Commands: `bvs4_kernelize thm` adds `thm.bvs4` with the statement of `thm`; `bvs4_module M` converts
every `bv_decide` axiom of an imported module `M` and re-proves the theorems of `M` that use them;
`bvs4_prep_module` / `bvs4_chunk` / `bvs4_assemble_module` do the same in shards (see below).

The SAT solver is CaDiCaL: by default the `cadical` executable in the directory of the running `lean`
executable (Lean toolchains ship it for `bv_decide`), or the path in the option `bvs4.cadical`. It is
run through the `timeout` command as `timeout <bvs4.timeout> cadical <cnf> <lrat> --lrat
--binary=true --quiet --shrink=0 --unsat`; its two files are written to `bvs4.workdir` (default: the
current directory) and removed afterwards unless `bvs4.keepFiles` is set.
-/
open Lean Meta Elab Command Std.Tactic.BVDecide

namespace BVS.Driver4

register_option bvs4.chunk : Nat := { defValue := 2000, descr := "maximal LRAT steps per declaration" }
register_option bvs4.chunkHints : Nat := { defValue := 20000, descr := "maximal hints per declaration" }
register_option bvs4.timeout : Nat := { defValue := 600, descr := "SAT solver timeout (s)" }
register_option bvs4.log : String := { defValue := "", descr := "progress log file (appended)" }
register_option bvs4.workdir : String := { defValue := "", descr := "directory for DIMACS/LRAT files" }
register_option bvs4.keepFiles : Bool := { defValue := false, descr := "keep the DIMACS/LRAT files" }
register_option bvs4.cadical : String :=
  { defValue := "", descr := "path of the cadical executable (default: next to the lean executable)" }

def logLine (msg : String) : CoreM Unit := do
  let path := bvs4.log.get (← getOptions)
  if path != "" then
    let h ← IO.FS.Handle.mk path .append
    h.putStrLn s!"[{(← IO.monoMsNow)}] {msg}"
    h.flush

/-! ## Terms for data -/

def boolE (b : Bool) : Expr := if b then mkConst ``Bool.true else mkConst ``Bool.false
def natTy : Expr := mkConst ``Nat
def litTy : Expr := mkApp2 (mkConst ``Prod [0, 0]) natTy (mkConst ``Bool)
def clTy : Expr := mkApp (mkConst ``List [0]) litTy
def hintTy : Expr := mkApp2 (mkConst ``Prod [0, 0]) natTy natTy
def hintsTy : Expr := mkApp (mkConst ``List [0]) hintTy
def stepsTy : Expr := mkApp (mkConst ``List [0]) hintsTy

def listE (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc) (mkApp (mkConst ``List.nil [0]) ty)

def clauseE (c : List (Nat × Bool)) : Expr :=
  listE litTy (c.map fun (v, b) => mkApp4 (mkConst ``Prod.mk [0, 0]) natTy (mkConst ``Bool) (mkRawNatLit v) (boolE b))

def hintsE (hs : List (Nat × Nat)) : Expr :=
  listE hintTy (hs.map fun (a, b) => mkApp4 (mkConst ``Prod.mk [0, 0]) natTy natTy (mkRawNatLit a) (mkRawNatLit b))

/-- The clause trie: the subtree whose relative key `j` is the absolute key `a * j + b`. -/
partial def trieE (m : Std.HashMap Nat (List (Nat × Bool))) (maxKey : Nat) : Expr :=
  go 1 0
where
  go (a b : Nat) : Expr :=
    if b > maxKey then mkApp (mkConst ``BVS.NT.nil) clTy
    else
      let v := match m.get? b with
        | some c => mkApp2 (mkConst ``Option.some [0]) clTy (clauseE c)
        | none => mkApp (mkConst ``Option.none [0]) clTy
      mkApp4 (mkConst ``BVS.NT.node) clTy v (go (2 * a) (a + b)) (go (2 * a) (2 * a + b))

instance : Inhabited Leaf := ⟨.cl []⟩

def ltTy : Expr := mkConst ``BVS.LTree
def leafTy : Expr := mkConst ``BVS.Leaf

def leafE : Leaf → Expr
  | .gt k l r j => mkApp4 (mkConst ``BVS.Leaf.gt) (mkRawNatLit k) (mkRawNatLit l) (mkRawNatLit r) (mkRawNatLit j)
  | .cl c => mkApp (mkConst ``BVS.Leaf.cl) (clauseE c)

/-- The perfect tree of depth `D` whose leaves are those with ids `0 … 2^D - 1`. -/
partial def treeE (m : Std.HashMap Nat Leaf) (maxKey D : Nat) : Expr := Id.run do
  let mut empties : Array Expr := #[mkApp (mkConst ``BVS.LTree.leaf) (mkApp (mkConst ``Option.none [0]) leafTy)]
  for _ in [0:D] do
    let e := empties.back!
    empties := empties.push (mkApp2 (mkConst ``BVS.LTree.node) e e)
  return go empties 0 D
where
  go (empties : Array Expr) (lo d : Nat) : Expr :=
    if lo > maxKey then empties[d]!
    else if d == 0 then
      match m.get? lo with
      | some c => mkApp (mkConst ``BVS.LTree.leaf) (mkApp2 (mkConst ``Option.some [0]) leafTy (leafE c))
      | none => empties[0]!
    else mkApp2 (mkConst ``BVS.LTree.node) (go empties lo (d - 1)) (go empties (lo + 2 ^ (d - 1)) (d - 1))

/-! ## SAT solving and the certificate -/

def dimacs (F : Array (List (Nat × Bool))) : String := Id.run do
  let maxv := F.foldl (fun m c => c.foldl (fun m (v, _) => max m v) m) 0
  let mut s := s!"p cnf {maxv + 1} {F.size}\n"
  for c in F do
    for (v, b) in c do
      s := s ++ (if b then s!"{v + 1} " else s!"-{v + 1} ")
    s := s ++ "0\n"
  return s

def cadicalPath : CoreM System.FilePath := do
  let p := bvs4.cadical.get (← getOptions)
  if p != "" then return System.FilePath.mk p
  return (← IO.appDir) / "cadical"

def removeQuietly (p : String) : IO Unit := do
  try IO.FS.removeFile p catch _ => pure ()

/-- Run CaDiCaL; returns the LRAT proof bytes on UNSAT. -/
def solve (F : Array (List (Nat × Bool))) (base : String) (timeout : Nat) : CoreM ByteArray := do
  let opts ← getOptions
  let dir := bvs4.workdir.get opts
  let dir := if dir == "" then "." else dir
  IO.FS.createDirAll dir
  let cnfPath := s!"{dir}/{base}.cnf"
  let lratPath := s!"{dir}/{base}.lrat"
  let keep := bvs4.keepFiles.get opts
  IO.FS.writeFile cnfPath (dimacs F)
  let out ← IO.Process.output { cmd := "timeout", args := #[toString timeout, (← cadicalPath).toString,
    cnfPath, lratPath, "--lrat", "--binary=true", "--quiet", "--shrink=0", "--unsat"] }
  unless out.stdout.startsWith "s UNSATISFIABLE" do
    unless keep do
      removeQuietly cnfPath
      removeQuietly lratPath
    throwError "bvs: the SAT solver did not report UNSAT (exit {out.exitCode}): {out.stdout.take 200}"
  let bytes ← IO.FS.readBinFile lratPath
  unless keep do
    removeQuietly cnfPath
    removeQuietly lratPath
  return bytes

def single (x : Nat) : Bool := x != 0 && (x &&& (x - 1)) == 0

def bitsOfClause (c : List (Nat × Bool)) : Nat × Nat :=
  c.foldl (fun (p : Nat × Nat) (v, b) => if b then (p.1 ||| (1 <<< v), p.2) else (p.1, p.2 ||| (1 <<< v))) (0, 0)

def ofLratLit (l : Int) : Nat × Bool := if l > 0 then (l.natAbs - 1, true) else (l.natAbs - 1, false)

structure Prepared where
  /-- learned clauses, ids `L+1, L+2, …`; the last one is empty -/
  learned : Array (List (Nat × Bool))
  /-- hints of each learned clause `(id, unit variable)` -/
  hints : Array (List (Nat × Nat))
  rat : Nat

/-- Keep the RUP steps that reach the empty clause, renumber them after the `L` original clauses,
and annotate every hint with the variable it makes unit (compiled replay of the kernel check). -/
def prepare (F : Array (List (Nat × Bool))) (acts : Array LRAT.IntAction) : Except String Prepared := Id.run do
  let L := F.size
  -- backward pass: the steps needed for the empty clause
  let mut needed : Std.HashSet Nat := {}
  let mut found := false
  let mut rat := 0
  for i in [0:acts.size] do
    let a := acts[acts.size - 1 - i]!
    match a with
    | .addEmpty id hints =>
      if !found then
        found := true; needed := needed.insert id
        for h in hints do needed := needed.insert h
    | .addRup id _ hints =>
      if found && needed.contains id then
        for h in hints do needed := needed.insert h
    | .addRat id _ _ _ _ =>
      if found && needed.contains id then rat := rat + 1
    | .del _ => pure ()
  if !found then return .error "no empty clause in the LRAT proof"
  if rat > 0 then return .error s!"{rat} RAT steps are needed (unsupported)"
  -- forward pass
  let mut store : Std.HashMap Nat (List (Nat × Bool)) := {}
  for i in [0:L] do store := store.insert (i + 1) F[i]!
  let mut ren : Std.HashMap Nat Nat := {}
  for i in [0:L] do ren := ren.insert (i + 1) (i + 1)
  let mut next := L + 1
  let mut learned : Array (List (Nat × Bool)) := #[]
  let mut hintsOut : Array (List (Nat × Nat)) := #[]
  for a in acts do
    let some (oid, cl, hints) := (match a with
      | .addRup id c h => some (id, c.toList.map ofLratLit, h)
      | .addEmpty id h => some (id, [], h)
      | _ => none) | continue
    unless needed.contains oid do continue
    let (cp, cn) := bitsOfClause cl
    let mut ann : Array (Nat × Nat) := #[]
    if (cp &&& cn) == 0 then
      let mut pa := cn
      let mut na := cp
      let mut done := false
      for h in hints do
        if done then break
        let some hid := ren.get? h | return .error s!"hint {h} of step {oid} is unknown"
        let some hc := store.get? hid | return .error s!"clause {hid} missing"
        let (hp, hn) := bitsOfClause hc
        if ((hp &&& pa) ||| (hn &&& na)) != 0 then continue   -- satisfied: useless
        let up := hp ^^^ (hp &&& (pa ||| na))
        let un := hn ^^^ (hn &&& (pa ||| na))
        -- annotation `k`: 0 conflict, `2u+1` positive unit `u`, `2u+2` negative unit `u`
        if up == 0 && un == 0 then ann := ann.push (hid, 0); done := true
        else if up == 0 && single un then ann := ann.push (hid, 2 * Nat.log2 un + 2); na := na ||| un
        else if un == 0 && single up then ann := ann.push (hid, 2 * Nat.log2 up + 1); pa := pa ||| up
        else continue   -- not unit: useless
      if !done then return .error s!"step {oid}: the replay found no conflict"
    store := store.insert next cl
    ren := ren.insert oid next
    next := next + 1
    learned := learned.push cl
    hintsOut := hintsOut.push ann.toList
    if cl.isEmpty then break
  return .ok { learned, hints := hintsOut, rat }

/-! ## Declarations -/

def addDefn (n : Name) (ty val : Expr) : CoreM Unit :=
  addDecl (.defnDecl { name := n, levelParams := [], type := ty, value := val, hints := .abbrev, safety := .safe })

/-- Add `n : e = true` proved by `rfl`, checked by the kernel; returns the time in ms. -/
def addTrueThm (n : Name) (e : Expr) : CoreM Nat := do
  let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e (mkConst ``Bool.true)
  let pf := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let t0 ← IO.monoMsNow
  withOptions (fun o => o.set `Elab.async false) <|
    addDecl (.thmDecl { name := n, levelParams := [], type := ty, value := pf })
  return (← IO.monoMsNow) - t0

structure Stats where
  nodes : Nat := 0
  clauses : Nat := 0
  vars : Nat := 0
  steps : Nat := 0
  hints : Nat := 0
  chunks : Nat := 0
  solveMs : Nat := 0
  prepMs : Nat := 0
  defMs : Nat := 0
  baseMs : Nat := 0
  chunkMs : Nat := 0
  maxChunkMs : Nat := 0

/-- Prove `E.Unsat` (`E : BVLogicalExpr` closed); returns the proof term and statistics. -/
def proveUnsat (base : Name) (E : Expr) : MetaM (Expr × Stats) := do
  let opts ← getOptions
  let chunk := max 1 (bvs4.chunk.get opts)
  let mut st : Stats := {}
  let t0 ← IO.monoMsNow
  let bv ← unsafe evalExpr BVLogicalExpr (mkConst ``BVLogicalExpr) E
  unless supportedBool bv do throwError "bvs: unsupported constructors in {toString bv |>.take 300}"
  let (bst, out) := blastBool St.empty bv
  let F := (cnfOf bst.es out).toArray
  st := { st with nodes := bst.n, clauses := F.size,
                  vars := F.foldl (fun m c => c.foldl (fun m (v, _) => max m (v + 1)) m) 0 }
  logLine s!"{base}: {st.nodes} nodes, CNF {F.size} clauses, {st.vars} variables"
  let t1 ← IO.monoMsNow
  -- unique file names (several processes may share the work directory)
  let tag := s!"{base.toString.replace "." "_"}_{← IO.monoNanosNow}"
  let proof ← solve F tag (bvs4.timeout.get opts)
  let acts ← match LRAT.parseLRATProof proof with
    | .ok a => pure a
    | .error e => throwError "bvs: LRAT parse error {e}"
  let t2 ← IO.monoMsNow
  let prep ← match prepare F acts with
    | .ok p => pure p
    | .error e => throwError "bvs: {e}"
  let L := F.size
  let N := L + prep.learned.size
  st := { st with solveMs := t2 - t1, steps := prep.learned.size,
                  hints := prep.hints.foldl (fun a h => a + h.length) 0 }
  -- the clause trie
  let mut m : Std.HashMap Nat Leaf := {}
  let lv := (leavesOf bst.es out).toArray
  unless lv.size == L do throwError "bvs: leaf count mismatch"
  for i in [0:L] do m := m.insert (i + 1) lv[i]!
  for i in [0:prep.learned.size] do m := m.insert (L + 1 + i) (.cl prep.learned[i]!)
  let tName := base ++ `_bvs_T
  let D := Nat.log2 (N + 1) + (if 2 ^ Nat.log2 (N + 1) < N + 1 then 1 else 0)
  let H := 2 ^ D / 2
  addDefn tName ltTy (treeE m N D)
  -- hint chunks
  let mut cnames : Array (Name × Nat × Nat) := #[]   -- (name, start id, count)
  let maxH := max 1 (bvs4.chunkHints.get opts)
  let mut i := 0
  let mut k := 0
  while i < prep.hints.size do
    -- a chunk: at most `chunk` steps and (unless a single step) at most `maxH` hints
    let mut j := i
    let mut h := 0
    while j < prep.hints.size && j - i < chunk && (j == i || h + prep.hints[j]!.length ≤ maxH) do
      h := h + prep.hints[j]!.length
      j := j + 1
    let part := (prep.hints.extract i j).toList
    let nm := base ++ Name.mkSimple s!"_bvs_s{k}"
    addDefn nm stepsTy (listE hintsTy (part.map hintsE))
    cnames := cnames.push (nm, L + 1 + i, part.length)
    i := j
    k := k + 1
  let t3 ← IO.monoMsNow
  st := { st with prepMs := t3 - t2, defMs := t3 - t2, chunks := cnames.size }
  logLine s!"{base}: {prep.learned.size} steps, {st.hints} hints, {cnames.size} chunks; solve {st.solveMs} ms"
  -- kernel: the base check
  let T := mkConst tName
  let lookE := mkApp2 (mkConst ``BVS.look4) T (mkRawNatLit H)
  let baseE := mkApp5 (mkConst ``BVS.check4) E T (mkRawNatLit D) (mkRawNatLit H) (mkRawNatLit L)
  let msB ← addTrueThm (base ++ `_bvs_base) baseE
  st := { st with baseMs := msB }
  logLine s!"{base}: base check (bit-blast + CNF + trie agreement) {msB} ms"
  -- kernel: the chunks
  let mut chain : Option Expr := none
  let mut cur := L + 1
  for (nm, s, cnt) in cnames do
    let thm := base ++ Name.mkSimple s!"{nm.getString!}_ok"
    let ms ← addTrueThm thm (mkApp3 (mkConst ``BVS.chkUR) lookE (mkRawNatLit s) (mkConst nm))
    st := { st with chunkMs := st.chunkMs + ms, maxChunkMs := max st.maxChunkMs ms }
    let c := mkApp4 (mkConst ``BVS.chkUR_sound) lookE (mkConst nm) (mkRawNatLit s) (mkConst thm)
    -- c : ChainOK T s (s + length) ; state it with literal endpoints
    let e := s + cnt
    chain := some <| match chain with
      | none => c
      | some ch => mkApp6 (mkConst ``BVS.ChainL.trans) lookE (mkRawNatLit (L + 1)) (mkRawNatLit cur) (mkRawNatLit e) ch c
    cur := e
    logLine s!"{base}: chunk {nm} ({cnt} steps from id {s}) {ms} ms"
  let some ch := chain | throwError "bvs: no steps"
  let msE ← addTrueThm (base ++ `_bvs_empty)
    (mkApp4 (mkConst ``BVS.stepEmpty4) T (mkRawNatLit D) (mkRawNatLit H) (mkRawNatLit N))
  let pf := mkAppN (mkConst ``BVS.bvs_unsat4) #[E, T, mkRawNatLit D, mkRawNatLit H, mkRawNatLit L, mkRawNatLit N,
    mkConst (base ++ `_bvs_base), ch, mkConst (base ++ `_bvs_empty)]
  let _ := msE
  return (pf, st)

def Stats.summary (s : Stats) : String :=
  s!"{s.nodes} nodes, {s.clauses} clauses, {s.vars} vars; {s.steps} steps, {s.hints} hints, {s.chunks} chunks; " ++
  s!"solve {s.solveMs} ms, prep+defs {s.defMs} ms; kernel: base {s.baseMs} ms, chunks {s.chunkMs} ms (max {s.maxChunkMs} ms)"

/-! ## Finding `bv_decide` proofs -/

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
    | none => throwError "bvs: {n} has no value"

def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Re-prove theorem `n` (proved with `bv_decide` in this file or an import): every
`unsat_of_verifyBVExpr_eq_true E C _` is replaced by a kernel-checked proof of `E.Unsat`; adds
`n.bvs` with the same statement. -/
def kernelize (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let v ← valueOf n
  let all := collectVerify v
  if all.isEmpty then throwError "bvs: no `unsat_of_verifyBVExpr_eq_true` in {n}"
  let mut repl : Std.HashMap Expr Expr := {}
  let mut idx := 0
  for e in all do
    if repl.contains e then continue
    idx := idx + 1
    let t0 ← IO.monoMsNow
    let (pf, st) ← proveUnsat (n ++ Name.mkSimple s!"_bvs4_{idx}") e.getAppArgs[0]!
    logInfo m!"bvs {n} #{idx}: {st.summary}; total {(← IO.monoMsNow) - t0} ms"
    repl := repl.insert e pf
  let v' := v.replace fun e => repl.get? e
  let t0 ← IO.monoMsNow
  addDecl (.thmDecl { name := n ++ `bvs4, levelParams := ci.levelParams, type := ci.type, value := v' })
  let axs ← collectAxioms (n ++ `bvs4)
  unless axs.all stdAxioms.contains do throwError "bvs: {n ++ `bvs4} uses non-standard axioms {axs.toList}"
  logInfo m!"bvs: added {n ++ `bvs4} ({(← IO.monoMsNow) - t0} ms to check the assembled theorem; axioms {axs.toList})"

elab "bvs4_kernelize " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) (kernelize n)

/-- The `bv_decide` axioms of an imported module (private names included). -/
def bvdAxioms (m : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? m | throwError "bvs: module {m} is not imported"
  let names := env.header.moduleData[idx.toNat]!.constNames
  return names.filter fun c =>
    (match env.find? c with | some (.axiomInfo _) => true | _ => false) &&
    (c.toString.splitOn "bv_decide.ax_").length > 1

/-- For every `bv_decide` axiom `ax : verifyBVExpr E C = true` of module `m`: prove `E.Unsat`
(theorem `bvsfact_<i>.unsat`), then re-prove the theorems of `m` that use `ax` (`bvsthm_<j>.bvs`). -/
def bvsModule (m : Name) : MetaM Unit := do
  let env ← getEnv
  let axs ← bvdAxioms m
  let some idx := env.getModuleIdx? m | throwError "bvs: module {m} is not imported"
  let thms := (env.header.moduleData[idx.toNat]!.constNames).filter fun c =>
    match env.find? c with | some (.thmInfo _) => true | _ => false
  logInfo m!"bvs {m}: {axs.size} bv_decide axioms"
  let mut i := 0
  let mut j := 0
  for ax in axs do
    i := i + 1
    let ty := (← getConstInfo ax).type
    let some (_, lhs, _) := ty.eq? | throwError "bvs: unexpected axiom type {ty}"
    unless lhs.isAppOfArity ``Reflect.verifyBVExpr 2 do throwError "bvs: unexpected axiom type {ty}"
    let E := lhs.getArg! 0
    let base := Name.mkSimple s!"bvs4fact_{i}"
    let t0 ← IO.monoMsNow
    let (pf, st) ← proveUnsat base E
    let fact := base ++ `unsat
    addDecl (.thmDecl { name := fact, levelParams := [], type := mkApp (mkConst ``BVLogicalExpr.Unsat) E, value := pf })
    let fax ← collectAxioms fact
    logInfo m!"bvs {ax}: {st.summary}; total {(← IO.monoMsNow) - t0} ms; axioms {fax.toList}"
    for t in thms do
      let some (.thmInfo tv) := (← getEnv).find? t | continue
      unless tv.value.getUsedConstants.contains ax do continue
      let v' := tv.value.replace fun e =>
        if e.isAppOfArity ``Reflect.unsat_of_verifyBVExpr_eq_true 3 && e.appArg! == mkConst ax then
          some (mkConst fact) else none
      if v'.getUsedConstants.contains ax then
        logInfo m!"bvs {t}: uses {ax} outside `unsat_of_verifyBVExpr_eq_true`; not rebuilt"
        continue
      j := j + 1
      let nm := (Name.mkSimple s!"bvs4thm_{j}") ++ `bvs
      addDecl (.thmDecl { name := nm, levelParams := tv.levelParams, type := tv.type, value := v' })
      let ta ← collectAxioms nm
      let same := ((← getConstInfo nm).type == tv.type)
      logInfo m!"bvs {t}: re-proved as {nm} (statement identical: {same}); axioms {ta.toList}"

elab "bvs4_module " id:ident : command => liftTermElabM do
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) (bvsModule id.getId)

/-! ## Sharded checking: the chunk theorems in separate modules, compiled in parallel

`bvs4_prep_module M "dir" k` (in a module `P`): for every `bv_decide` axiom of `M`, runs the
untrusted pipeline, defines the clause tree and the hint chunks, proves the base check and the empty
clause, and records the chunk table (`_bvs_meta`) and dimensions (`_bvs_dims`). It writes `k` shard
files `dir/<P>_S<r>.lean` (each `import P` and `bvs4_chunk …` lines) and `dir/<P>_Final.lean`
(importing the shards, `bvs4_assemble_module M`). The shards are independent and can be compiled in
parallel; each holds only its chunk theorems. -/

/-- Phase A: the untrusted pipeline, the data, the base check and the empty clause. Returns the
chunk table `(start id, count)`. -/
def prepFact (base : Name) (E : Expr) : MetaM (Array (Nat × Nat)) := do
  let opts ← getOptions
  let chunk := max 1 (bvs4.chunk.get opts)
  let bv ← unsafe evalExpr BVLogicalExpr (mkConst ``BVLogicalExpr) E
  unless supportedBool bv do throwError "bvs: unsupported constructors in {toString bv |>.take 300}"
  let (bst, out) := blastBool St.empty bv
  let F := (cnfOf bst.es out).toArray
  logLine s!"{base}: {bst.n} nodes, CNF {F.size} clauses"
  let tag := s!"{base.toString.replace "." "_"}_{← IO.monoNanosNow}"
  let t1 ← IO.monoMsNow
  let proof ← solve F tag (bvs4.timeout.get opts)
  let acts ← match LRAT.parseLRATProof proof with
    | .ok a => pure a
    | .error e => throwError "bvs: LRAT parse error {e}"
  let prep ← match prepare F acts with
    | .ok p => pure p
    | .error e => throwError "bvs: {e}"
  let L := F.size
  let N := L + prep.learned.size
  let mut m : Std.HashMap Nat Leaf := {}
  let lv := (leavesOf bst.es out).toArray
  for i in [0:L] do m := m.insert (i + 1) lv[i]!
  for i in [0:prep.learned.size] do m := m.insert (L + 1 + i) (.cl prep.learned[i]!)
  let D := Nat.log2 (N + 1) + (if 2 ^ Nat.log2 (N + 1) < N + 1 then 1 else 0)
  let H := 2 ^ D / 2
  addDefn (base ++ `_bvs_T) ltTy (treeE m N D)
  let mut table : Array (Nat × Nat) := #[]
  let maxH := max 1 (bvs4.chunkHints.get opts)
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
  let T := mkConst (base ++ `_bvs_T)
  let msB ← addTrueThm (base ++ `_bvs_base) (mkApp5 (mkConst ``BVS.check4) E T (mkRawNatLit D) (mkRawNatLit H) (mkRawNatLit L))
  logLine s!"{base}: base check {msB} ms"
  let _ ← addTrueThm (base ++ `_bvs_empty) (mkApp4 (mkConst ``BVS.stepEmpty4) T (mkRawNatLit D) (mkRawNatLit H) (mkRawNatLit N))
  return table

/-- Read a list literal (`List.cons … List.nil`) from a definition's value. -/
partial def listLit (e : Expr) : MetaM (List Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``List.nil 1 then return []
  if e.isAppOfArity ``List.cons 3 then return e.getArg! 1 :: (← listLit (e.getArg! 2))
  throwError "bvs: not a list literal: {e}"

def natLitOf (e : Expr) : MetaM Nat := do
  match e.consumeMData with
  | .lit (.natVal n) => return n
  | e => throwError "bvs: not a numeral: {e}"

def readMeta (base : Name) : MetaM (Array (Nat × Nat) × Nat × Nat × Nat × Nat) := do
  let some mv := (← getConstInfo (base ++ `_bvs_meta)).value? | throwError "bvs: no table"
  let some dv := (← getConstInfo (base ++ `_bvs_dims)).value? | throwError "bvs: no dims"
  let tbl ← (← listLit mv).mapM fun p => do
    unless p.isAppOfArity ``Prod.mk 4 do throwError "bvs: bad table entry {p}"
    return (← natLitOf (p.getArg! 2), ← natLitOf (p.getArg! 3))
  let dims ← (← listLit dv).mapM natLitOf
  let [D, H, L, N] := dims | throwError "bvs: bad dims"
  return (tbl.toArray, D, H, L, N)

/-- Phase B: chunk `j`. -/
def chunkFact (base : Name) (j : Nat) : MetaM Nat := do
  let (tbl, _, H, _, _) ← readMeta base
  let some (s, _) := tbl[j]? | throwError "bvs: no chunk {j}"
  let lookE := mkApp2 (mkConst ``BVS.look4) (mkConst (base ++ `_bvs_T)) (mkRawNatLit H)
  addTrueThm (base ++ Name.mkSimple s!"_bvs_s{j}_ok")
    (mkApp3 (mkConst ``BVS.chkUR) lookE (mkRawNatLit s) (mkConst (base ++ Name.mkSimple s!"_bvs_s{j}")))

/-- Phase C: the proof of `E.Unsat` from the chunk theorems. -/
def assembleFact (base : Name) (E : Expr) : MetaM Expr := do
  let (tbl, D, H, L, N) ← readMeta base
  let T := mkConst (base ++ `_bvs_T)
  let lookE := mkApp2 (mkConst ``BVS.look4) T (mkRawNatLit H)
  let mut chain : Option Expr := none
  let mut cur := L + 1
  for j in [0:tbl.size] do
    let (s, cnt) := tbl[j]!
    let c := mkApp4 (mkConst ``BVS.chkUR_sound) lookE (mkConst (base ++ Name.mkSimple s!"_bvs_s{j}"))
      (mkRawNatLit s) (mkConst (base ++ Name.mkSimple s!"_bvs_s{j}_ok"))
    let e := s + cnt
    chain := some <| match chain with
      | none => c
      | some ch => mkApp6 (mkConst ``BVS.ChainL.trans) lookE (mkRawNatLit (L + 1)) (mkRawNatLit cur) (mkRawNatLit e) ch c
    cur := e
  let some ch := chain | throwError "bvs: no steps"
  return mkAppN (mkConst ``BVS.bvs_unsat4) #[E, T, mkRawNatLit D, mkRawNatLit H, mkRawNatLit L, mkRawNatLit N,
    mkConst (base ++ `_bvs_base), ch, mkConst (base ++ `_bvs_empty)]

elab "bvs4_prep_module " id:ident dir:str k:num : command => liftTermElabM do
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let m := id.getId
  let axs ← bvdAxioms m
  let me := (← getEnv).mainModule
  let k := max 1 k.getNat
  let mut jobs : Array (Array (Name × Nat)) := Array.replicate k #[]
  let mut r := 0
  let mut i := 0
  for ax in axs do
    i := i + 1
    let ty := (← getConstInfo ax).type
    let some (_, lhs, _) := ty.eq? | throwError "bvs: unexpected axiom type {ty}"
    let E := lhs.getArg! 0
    let base := Name.mkSimple s!"bvs4fact_{i}"
    let table ← prepFact base E
    for j in [0:table.size] do
      jobs := jobs.modify r (·.push (base, j))
      r := (r + 1) % k
  let d := dir.getString
  let pre := me.toString
  for q in [0:k] do
    let lines := jobs[q]!.toList.map fun (b, j) => s!"bvs4_chunk {b} {j}"
    IO.FS.writeFile s!"{d}/{pre}_S{q}.lean" (String.intercalate "\n"
      ([s!"import {pre}", "set_option maxHeartbeats 0"] ++ lines) ++ "\n")
  IO.FS.writeFile s!"{d}/{pre}_Final.lean" (String.intercalate "\n"
    ((List.range k).map (fun q => s!"import {pre}_S{q}") ++ ["set_option maxHeartbeats 0", s!"bvs4_assemble_module {m}"]) ++ "\n")
  logInfo m!"bvs: {axs.size} facts prepared; {k} shard files and {pre}_Final.lean written to {d}"

elab "bvs4_chunk " id:ident j:num : command => liftTermElabM do
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let ms ← chunkFact id.getId j.getNat
  logLine s!"{id.getId}: shard chunk {j.getNat} {ms} ms"

elab "bvs4_assemble_module " id:ident : command => liftTermElabM do
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let m := id.getId
  let env ← getEnv
  let axs ← bvdAxioms m
  let some idx := env.getModuleIdx? m | throwError "bvs: module {m} is not imported"
  let thms := (env.header.moduleData[idx.toNat]!.constNames).filter fun c =>
    match env.find? c with | some (.thmInfo _) => true | _ => false
  let mut i := 0
  let mut j := 0
  for ax in axs do
    i := i + 1
    let ty := (← getConstInfo ax).type
    let some (_, lhs, _) := ty.eq? | throwError "bvs: unexpected axiom type {ty}"
    let E := lhs.getArg! 0
    let base := Name.mkSimple s!"bvs4fact_{i}"
    let pf ← assembleFact base E
    let fact := base ++ `unsat
    let t0 ← IO.monoMsNow
    addDecl (.thmDecl { name := fact, levelParams := [], type := mkApp (mkConst ``BVLogicalExpr.Unsat) E, value := pf })
    logInfo m!"bvs {ax}: assembled {fact} ({(← IO.monoMsNow) - t0} ms); axioms {(← collectAxioms fact).toList}"
    for t in thms do
      let some (.thmInfo tv) := (← getEnv).find? t | continue
      unless tv.value.getUsedConstants.contains ax do continue
      let v' := tv.value.replace fun e =>
        if e.isAppOfArity ``Reflect.unsat_of_verifyBVExpr_eq_true 3 && e.appArg! == mkConst ax then
          some (mkConst fact) else none
      if v'.getUsedConstants.contains ax then continue
      j := j + 1
      let nm := (Name.mkSimple s!"bvs4thm_{j}") ++ `bvs
      addDecl (.thmDecl { name := nm, levelParams := tv.levelParams, type := tv.type, value := v' })
      logInfo m!"bvs {t}: re-proved as {nm} (statement identical: {(← getConstInfo nm).type == tv.type}); axioms {(← collectAxioms nm).toList}"

end BVS.Driver4
