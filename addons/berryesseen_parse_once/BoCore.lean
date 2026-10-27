import NativeTrust
import BeList
set_option Elab.async false

/-!
# BerryOpt: parse a cover certificate once, then check the pieces against the parsed constant

The split pieces of the strings add-on (`BeSplitL`) each evaluate
`obsOfParse … (parseCoverL 64 (tokensL [c₁, …]))`: every piece re-parses the whole certificate string
(1.2 MB for `Small.Data.Cover3`). Here the parse is done once ("certified literalization"):

* `bo_tree P D`: compiled (untrusted) code reads the string `D` and adds one definition per node of
  the cover tree, `P.t<i>` (preorder), whose value is the node in the exact shape `parseCoverL`
  produces (rationals as `(z : Rat) / (d : Rat)`, choices as `choiceOf k`); plus the character lists
  `P.c<j>` of the string's literal pieces.
* `bo_parse P F`: one kernel declaration `P.hpL : parseCoverL 64 (tokensL (P.c1 ++ …)) = some (P.t0, [])`
  (the only evaluation of the parser), then `P.parse : f … D = coverAccepted… n … P.t0` for the
  native fact `F : f … D = true`.
* `bo_leaves P F a b`: the leaves `a ≤ k < b` (in preorder): `P.leaf<i> : coverAccepted… n bounds P.t<i> = true`,
  one kernel declaration each; no piece mentions the string.
* `bo_assemble P F`: each split node `P.node<i>` from its children and its split-point test (two
  rational comparisons, evaluated by the kernel), then `P.final : f … D = true`.

Nothing computed by compiled code enters a proof unchecked: the tree is a definition, and the
kernel checks `parseCoverL … = some (P.t0, [])` by evaluation. Only standard axioms are used.
-/

namespace BerryOpt

open Lean Meta Elab Command
open BerryEsseen.Upper0423.Native NativeTrust.BE

/-! ## Lemmas -/

theorem coverAccepted_split_true {n : Nat} {dl dh wl wh m : Rat} {L R : Cover}
    (h : (decide (wl < m) && decide (m < wh)) = true)
    (hL : coverAccepted n dl dh wl m L = true) (hR : coverAccepted n dl dh m wh R = true) :
    coverAccepted n dl dh wl wh (.split true m L R) = true := by
  rw [coverAccepted.eq_2]
  simp only [ite_true, h, hL, hR, Bool.and_self]

theorem coverAccepted_split_false {n : Nat} {dl dh wl wh m : Rat} {L R : Cover}
    (h : (decide (dl < m) && decide (m < dh)) = true)
    (hL : coverAccepted n dl m wl wh L = true) (hR : coverAccepted n m dh wl wh R = true) :
    coverAccepted n dl dh wl wh (.split false m L R) = true := by
  rw [coverAccepted.eq_2]
  simp only [Bool.false_eq_true, ite_false, h, hL, hR, Bool.and_self]

theorem coverAcceptedBE_split_true {n : Nat} {bl bh el eh m : Rat} {L R : Cover}
    (h : (decide (el < m) && decide (m < eh)) = true)
    (hL : coverAcceptedBE n bl bh el m L = true) (hR : coverAcceptedBE n bl bh m eh R = true) :
    coverAcceptedBE n bl bh el eh (.split true m L R) = true := by
  rw [coverAcceptedBE.eq_2]
  simp only [ite_true, h, hL, hR, Bool.and_self]

theorem coverAcceptedBE_split_false {n : Nat} {bl bh el eh m : Rat} {L R : Cover}
    (h : (decide (bl < m) && decide (m < bh)) = true)
    (hL : coverAcceptedBE n bl m el eh L = true) (hR : coverAcceptedBE n m bh el eh R = true) :
    coverAcceptedBE n bl bh el eh (.split false m L R) = true := by
  rw [coverAcceptedBE.eq_2]
  simp only [Bool.false_eq_true, ite_false, h, hL, hR, Bool.and_self]

theorem toList_append_of {s t : String} {L M : List Char} (hs : s.toList = L) (ht : t.toList = M) :
    (s ++ t).toList = L ++ M := by
  rw [String.toList_append, hs, ht]

theorem flat_lit {s : String} {c R : List Char} (h : s.toList = c) : s.toList ++ R = c ++ R := by
  rw [h]

theorem flat_app {a b : String} {R Rb Rab : List Char} (hb : b.toList ++ R = Rb)
    (ha : a.toList ++ Rb = Rab) : (a ++ b).toList ++ R = Rab := by
  rw [String.toList_append, List.append_assoc, hb, ha]

theorem flat_top {s : String} {L : List Char} (h : s.toList ++ [] = L) : s.toList = L := by
  rw [← h, List.append_nil]

theorem parse_bridge {s : String} {L : List Char} {r : Option (Cover × List (List Char))}
    (hs : s.toList = L) (hL : parseCoverL 64 (tokensL L) = r) :
    parseCoverL 64 (tokensL s.toList) = r := hs ▸ hL

theorem coverStringAccepted_of_parse {n : Nat} {s : String} {cov : Cover}
    (hp : parseCoverL 64 (tokensL s.toList) = some (cov, [])) :
    coverStringAccepted n s = coverAccepted n 0 deltaMax 0 1 cov := by
  rw [coverStringAccepted_eq]
  unfold coverListAccepted
  rw [hp]

theorem coverStringAcceptedDW_of_parse {n : Nat} {dlo dhi : Rat} {s : String} {cov : Cover}
    (hp : parseCoverL 64 (tokensL s.toList) = some (cov, [])) :
    coverStringAcceptedDW n dlo dhi s = coverAccepted n dlo dhi 0 1 cov := by
  rw [coverStringAcceptedDW_eq]
  unfold coverListAcceptedDW
  rw [hp]

theorem coverStringAcceptedBE_of_parse {n : Nat} {blo bhi : Rat} {s : String} {cov : Cover}
    (hp : parseCoverL 64 (tokensL s.toList) = some (cov, [])) :
    coverStringAcceptedBE n blo bhi s = coverAcceptedBE n blo bhi 0 1 cov := by
  rw [coverStringAcceptedBE_eq]
  unfold coverListAcceptedBE
  rw [hp]

/-! ## Untrusted reader (compiled code): the string's tree as expressions in the parser's shape -/

/-- A cover tree whose leaves and split points are already expressions. -/
inductive MCov where
  | leaf (d : Expr)
  | split (axis : Bool) (m : Expr) (l r : MCov)
  deriving Inhabited

def MCov.size : MCov → Nat
  | .leaf _ => 1
  | .split _ _ l r => 1 + l.size + r.size

/-- Split on `' '` and `'\n'`, drop empty pieces (as `tokensL`). -/
def tokenize (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur : List Char := []
  for c in s.toList do
    if c == ' ' || c == '\n' then
      unless cur.isEmpty do
        out := out.push (String.ofList cur.reverse)
        cur := []
    else
      cur := c :: cur
  unless cur.isEmpty do
    out := out.push (String.ofList cur.reverse)
  return out

def natOfChars? (cs : List Char) : Option Nat :=
  if cs.isEmpty || !cs.all Char.isDigit then none
  else some (cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)

structure Shapes where
  /-- `fun (z : Int) (d : Nat) => (z : Rat) / (d : Rat)` -/
  ratDiv : Expr
  /-- `fun (z : Int) => (z : Rat)` -/
  ratInt : Expr

/-- The integer as `toIntL?` builds it: `Int.ofNat k`, or `Int.negOfNat k` after a `-`. -/
def intExpr? (cs : List Char) : Option Expr :=
  match cs with
  | '-' :: rest => (natOfChars? rest).map fun k => mkApp (mkConst ``Int.negOfNat) (mkRawNatLit k)
  | _ => (natOfChars? cs).map fun k => mkApp (mkConst ``Int.ofNat) (mkRawNatLit k)

/-- A rational token as `parseRatL` builds it. -/
def ratExpr? (sh : Shapes) (t : String) : Option Expr :=
  match t.toList.splitOn '/' with
  | [a] => (intExpr? a).map fun z => sh.ratInt.beta #[z]
  | [a, b] => do
    let z ← intExpr? a
    let d ← natOfChars? b
    if d = 0 then none else some (sh.ratDiv.beta #[z, mkRawNatLit d])
  | _ => none

def natTok? (t : String) : Option Nat := natOfChars? t.toList

abbrev ReadM := StateT Nat (Except String)

def next (toks : Array String) : ReadM String := do
  let i ← get
  match toks[i]? with
  | some t => set (i + 1); return t
  | none => throw s!"unexpected end of tokens at {i}"

def needRat (sh : Shapes) (toks : Array String) : ReadM Expr := do
  let t ← next toks
  match ratExpr? sh t with
  | some e => return e
  | none => throw s!"bad rational token `{t}` at {(← get) - 1}"

def needNat (toks : Array String) : ReadM Nat := do
  let t ← next toks
  match natTok? t with
  | some k => return k
  | none => throw s!"bad natural token `{t}` at {(← get) - 1}"

def mkList (α : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x t => mkApp3 (mkConst ``List.cons [Level.zero]) α x t) (mkApp (mkConst ``List.nil [Level.zero]) α)

def readPanels (sh : Shapes) (toks : Array String) (k : Nat) : ReadM Expr := do
  let ratT := mkConst ``Rat
  let choiceT := mkConst ``BerryEsseen.Upper0423.Native.Choice
  let mut xs := #[]
  for _ in [0:k] do
    let q ← needRat sh toks
    let c ← needNat toks
    xs := xs.push (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) ratT choiceT q
      (mkApp (mkConst ``BerryEsseen.Upper0423.Native.choiceOf) (mkRawNatLit c)))
  return mkList (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) ratT choiceT) xs

def readEnds (sh : Shapes) (toks : Array String) (k : Nat) : ReadM Expr := do
  let mut xs := #[]
  for _ in [0:k] do
    xs := xs.push (← needRat sh toks)
  return mkList (mkConst ``Rat) xs

/-- Mirrors `parseCoverL` (prefix form, fuel 64). -/
partial def readCover (sh : Shapes) (toks : Array String) (fuel : Nat) : ReadM MCov := do
  if fuel == 0 then throw "fuel exhausted (tree deeper than 63)"
  let t ← next toks
  if t == "S" then
    let axis ← next toks
    let m ← needRat sh toks
    let l ← readCover sh toks (fuel - 1)
    let r ← readCover sh toks (fuel - 1)
    return .split (axis == "1") m l r
  else if t == "F" then
    let c ← needRat sh toks
    let tau ← needRat sh toks
    let kl ← needNat toks
    let low ← readPanels sh toks kl
    let kh ← needNat toks
    let high ← readPanels sh toks kh
    let kn ← needNat toks
    let normal ← readEnds sh toks kn
    return .leaf (mkAppN (mkConst ``BerryEsseen.Upper0423.Native.LeafData.mk) #[c, tau, low, high, normal])
  else throw s!"unexpected token `{t}` at {(← get) - 1}"

/-- The literal pieces of a string-valued expression `"…" ++ "…" ++ …`. -/
partial def strPieces (e : Expr) : MetaM (Array String) := do
  match e with
  | .lit (.strVal s) => return #[s]
  | .mdata _ e => strPieces e
  | _ =>
    if e.isAppOfArity ``HAppend.hAppend 6 then
      return (← strPieces (e.getArg! 4)) ++ (← strPieces (e.getArg! 5))
    else if e.isAppOfArity ``String.append 2 then
      return (← strPieces (e.getArg! 0)) ++ (← strPieces (e.getArg! 1))
    else throwError "BerryOpt: unsupported string expression{indentExpr e}"

def elabShapes : TermElabM Shapes := do
  let d ← Term.elabTerm (← `(fun (z : Int) (d : Nat) => ((z : Rat) / (d : Rat)))) none
  let i ← Term.elabTerm (← `(fun (z : Int) => (z : Rat))) none
  Term.synthesizeSyntheticMVarsNoPostponing
  return { ratDiv := ← instantiateMVars d, ratInt := ← instantiateMVars i }

/-- Print a line to standard error at once (survives a later kill). -/
def note (s : String) : IO Unit := NativeTrust.eprintRaw s!"BO {s}"

def tName (pre : Name) (i : Nat) : Name := pre ++ (`t).appendIndexAfter i

def addDefn (name : Name) (type value : Expr) : CoreM Unit := do
  let env ← getEnv
  let h := getMaxHeight env value + 1
  NativeTrust.addDeclSync <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular h, safety := .safe }

/-- Add the node definitions of `t` in post-order (children first), named by preorder index. -/
partial def addNodes (pre : Name) (t : MCov) (i : Nat) : CoreM Unit := do
  let coverT := mkConst ``BerryEsseen.Upper0423.Native.Cover
  match t with
  | .leaf d => addDefn (pre ++ (`t).appendIndexAfter i) coverT (mkApp (mkConst ``BerryEsseen.Upper0423.Native.Cover.leaf) d)
  | .split axis m l r =>
    let il := i + 1
    let ir := i + 1 + l.size
    addNodes pre l il
    addNodes pre r ir
    let b := if axis then mkConst ``Bool.true else mkConst ``Bool.false
    addDefn (pre ++ (`t).appendIndexAfter i) coverT
      (mkApp4 (mkConst ``BerryEsseen.Upper0423.Native.Cover.split) b m
        (mkConst (pre ++ (`t).appendIndexAfter il)) (mkConst (pre ++ (`t).appendIndexAfter ir)))

/-- `bo_tree P D`: node definitions `P.t<i>` and character lists `P.c<j>` for the string constant `D`. -/
syntax (name := boTreeCmd) "bo_tree " ident ident : command

@[command_elab boTreeCmd] def elabBoTree : CommandElab := fun stx => liftTermElabM do
  let pre := stx[1].getId
  let dataName ← realizeGlobalConstNoOverloadWithInfo stx[2]
  let some (.defnInfo d) := (← getEnv).find? dataName | throwError "`{dataName}` is not a definition"
  let t0 ← IO.monoMsNow
  let pieces ← strPieces d.value
  let s := String.join pieces.toList
  let toks := tokenize s
  let sh ← elabShapes
  let tree ← match (readCover sh toks 64).run 0 with
    | .ok (tree, k) =>
      unless k == toks.size do throwError "BerryOpt: {toks.size - k} tokens left after the cover"
      pure tree
    | .error msg => throwError "BerryOpt: cannot read the cover: {msg}"
  let t1 ← IO.monoMsNow
  addNodes pre tree 0
  let listChar := mkApp (mkConst ``List [Level.zero]) (mkConst ``Char)
  for j in [0:pieces.size] do
    addDefn (pre ++ (`c).appendIndexAfter (j + 1)) listChar (NativeTrust.charListExpr pieces[j]!)
  let t2 ← IO.monoMsNow
  note s!"tree {pre} chars={s.length} pieces={pieces.size} tokens={toks.size} nodes={tree.size} read_ms={t1 - t0} add_ms={t2 - t1}"
  logInfo m!"{pre}: {tree.size} nodes, {pieces.size} literal pieces, {s.length} characters"

/-! ## Walking the tree from the definitions -/

/-- Which acceptance function a native fact uses. -/
inductive Kind where
  | plain | dw | be
  deriving BEq, Inhabited

structure FactInfo where
  kind : Kind
  /-- `f … D` (the left side of the fact). -/
  lhs : Expr
  n : Expr
  data : Expr
  /-- extra arguments (`dlo dhi` or `blo bhi`). -/
  extra : Array Expr

def factInfo (fact : Name) : MetaM FactInfo := do
  let info ← getConstInfo fact
  let some (_, lhs, rhs) := info.type.eq? | throwError "`{fact}` is not an equation"
  unless rhs.isConstOf ``Bool.true do throwError "`{fact}` is not `… = true`"
  let args := lhs.getAppArgs
  match lhs.getAppFn with
  | .const ``coverStringAccepted _ =>
    return { kind := .plain, lhs, n := args[0]!, data := args[1]!, extra := #[] }
  | .const ``coverStringAcceptedDW _ =>
    return { kind := .dw, lhs, n := args[0]!, data := args[3]!, extra := #[args[1]!, args[2]!] }
  | .const ``coverStringAcceptedBE _ =>
    return { kind := .be, lhs, n := args[0]!, data := args[3]!, extra := #[args[1]!, args[2]!] }
  | _ => throwError "`{fact}`: unsupported acceptance function{indentExpr lhs}"

def ofParseLemma : Kind → Name
  | .plain => ``coverStringAccepted_of_parse
  | .dw => ``coverStringAcceptedDW_of_parse
  | .be => ``coverStringAcceptedBE_of_parse

def accFn : Kind → Name
  | .be => ``coverAcceptedBE
  | _ => ``coverAccepted

def splitLemma (k : Kind) (axis : Bool) : Name :=
  match k, axis with
  | .be, true => ``coverAcceptedBE_split_true
  | .be, false => ``coverAcceptedBE_split_false
  | _, true => ``coverAccepted_split_true
  | _, false => ``coverAccepted_split_false

/-- `P.parse`'s proof skeleton: `ofParse … hp : lhs = acc n b₁ b₂ b₃ b₄ P.t0` (with `hp` given). -/
def ofParseApp (fi : FactInfo) (cov hp : Expr) : Expr :=
  mkAppN (mkConst (ofParseLemma fi.kind)) (#[fi.n] ++ fi.extra ++ #[fi.data, cov, hp])

/-- The root bounds `b₁ b₂ b₃ b₄`, read off the conclusion of the `*_of_parse` lemma. -/
def rootBounds (fi : FactInfo) (pre : Name) : MetaM (Array Expr) := do
  let lem ← getConstInfo (ofParseLemma fi.kind)
  let args := #[fi.n] ++ fi.extra ++ #[fi.data, mkConst (tName pre 0)]
  let ty ← instantiateForall lem.type args
  let .forallE _ _ body _ := ty | throwError "unexpected lemma type{indentExpr ty}"
  let some (_, _, rhs) := body.eq? | throwError "unexpected lemma conclusion{indentExpr body}"
  return rhs.getAppArgs[1:5].toArray

/-- One node: preorder index, bounds, and either the leaf or the split (axis, point, children). -/
structure Node where
  idx : Nat
  bounds : Array Expr
  split? : Option (Bool × Expr × Nat × Nat)
  deriving Inhabited

/-- Walk the subtree at node `i` with bounds `b`, appending its nodes in preorder. -/
partial def walkGo (env : Environment) (pre : Name) (i : Nat) (b : Array Expr) (acc : Array Node) :
    MetaM (Array Node × Nat) := do
  let some (.defnInfo d) := env.find? (tName pre i)
    | throwError "missing node definition {tName pre i}"
  let v := d.value
  if v.isAppOfArity ``BerryEsseen.Upper0423.Native.Cover.leaf 1 then
    return (acc.push { idx := i, bounds := b, split? := none }, i + 1)
  else if v.isAppOfArity ``BerryEsseen.Upper0423.Native.Cover.split 4 then
    let axis := (v.getArg! 0).isConstOf ``Bool.true
    let m := v.getArg! 1
    let (b1, b2, b3, b4) := (b[0]!, b[1]!, b[2]!, b[3]!)
    let (bl, br) := if axis then (#[b1, b2, b3, m], #[b1, b2, m, b4]) else (#[b1, m, b3, b4], #[m, b2, b3, b4])
    let me := acc.size
    let acc := acc.push default
    let (acc, j) ← walkGo env pre (i + 1) bl acc
    let (acc, k) ← walkGo env pre j br acc
    return (acc.set! me { idx := i, bounds := b, split? := some (axis, m, i + 1, j) }, k)
  else throwError "unexpected node {tName pre i}{indentExpr v}"

/-- The nodes in preorder, from the definitions `P.t<i>`. -/
def walk (pre : Name) (rootB : Array Expr) : MetaM (Array Node) := do
  let (nodes, _) ← walkGo (← getEnv) pre 0 rootB #[]
  return nodes

def boolTrue : Expr := mkConst ``Bool.true

def mkEqTrue (e : Expr) : Expr := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) e boolTrue

def reflTrue : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) boolTrue

/-- `acc n b₁ b₂ b₃ b₄ P.t<i> = true` -/
def nodeStmt (fi : FactInfo) (pre : Name) (nd : Node) : Expr :=
  mkEqTrue (mkAppN (mkConst (accFn fi.kind)) (#[fi.n] ++ nd.bounds ++ #[mkConst (pre ++ (`t).appendIndexAfter nd.idx)]))

/-- Add a theorem; the kernel checks it now. Returns the kernel time in ms. -/
def addThm (name : Name) (type value : Expr) : CoreM Nat := do
  let t0 ← IO.monoMsNow
  withOptions (fun o => maxHeartbeats.set (maxRecDepth.set o 1000000) 0) do
    NativeTrust.addDeclSync <| .thmDecl { name, levelParams := [], type, value }
  return (← IO.monoMsNow) - t0

def listCharT : Expr := mkApp (mkConst ``List [Level.zero]) (mkConst ``Char)

/-- `a ++ b` on `List Char`. -/
def appL (a b : Expr) : Expr :=
  mkApp6 (mkConst ``HAppend.hAppend [Level.zero, Level.zero, Level.zero]) listCharT listCharT listCharT
    (mkApp2 (mkConst ``instHAppendOfAppend [Level.zero]) listCharT (mkApp (mkConst ``List.instAppend [Level.zero]) (mkConst ``Char))) a b

/-- For a string expression `"…" ++ "…" ++ …`: the list `P.c1 ++ P.c2 ++ …` (same association) and a
proof of `s.toList = …` (each piece by `String.toList_ofList`, checked by the kernel's literal unfolding). -/
partial def bridgeStr (pre : Name) (counter : IO.Ref Nat) (e : Expr) : MetaM (Expr × Expr × Expr) := do
  match e with
  | .lit (.strVal _) =>
    let j ← counter.modifyGet fun j => (j + 1, j + 1)
    let c := mkConst (pre ++ (`c).appendIndexAfter j)
    return (e, c, mkApp (mkConst ``String.toList_ofList) c)
  | .mdata _ e => bridgeStr pre counter e
  | _ =>
    if e.isAppOfArity ``HAppend.hAppend 6 then
      let (a, la, pa) ← bridgeStr pre counter (e.getArg! 4)
      let (b, lb, pb) ← bridgeStr pre counter (e.getArg! 5)
      return (e, appL la lb, mkAppN (mkConst ``toList_append_of) #[a, b, la, lb, pa, pb])
    else throwError "BerryOpt: unsupported string expression{indentExpr e}"

partial def countLits (e : Expr) : Nat :=
  match e with
  | .lit (.strVal _) => 1
  | .mdata _ e => countLits e
  | _ => if e.isAppOfArity ``HAppend.hAppend 6 then countLits (e.getArg! 4) + countLits (e.getArg! 5) else 0

/-- Right-associated form: `(flat, proof of e.toList ++ R = flat)` with `flat = P.c_j ++ (P.c_{j+1} ++ (… ++ R))`
(each character then passes through one `List.append` only, instead of up to `k - 1` in the left-associated
form of `D`'s value). -/
partial def bridgeR (pre : Name) (j : Nat) (e R : Expr) : MetaM (Expr × Expr) := do
  match e with
  | .lit (.strVal _) =>
    let c := mkConst (pre ++ (`c).appendIndexAfter j)
    return (appL c R, mkAppN (mkConst ``flat_lit) #[e, c, R, mkApp (mkConst ``String.toList_ofList) c])
  | .mdata _ e => bridgeR pre j e R
  | _ =>
    if e.isAppOfArity ``HAppend.hAppend 6 then
      let a := e.getArg! 4
      let b := e.getArg! 5
      let (Rb, hb) ← bridgeR pre (j + countLits a) b R
      let (Rab, ha) ← bridgeR pre j a Rb
      return (Rab, mkAppN (mkConst ``flat_app) #[a, b, R, Rb, Rab, hb, ha])
    else throwError "BerryOpt: unsupported string expression{indentExpr e}"

/-- `bo_parse P F`: `P.hpL` (the kernel parses the string once) and `P.parse : lhs = acc … P.t0`. -/
syntax (name := boParseCmd) "bo_parse " ident ident : command

@[command_elab boParseCmd] def elabBoParse : CommandElab := fun stx => liftTermElabM do
  let pre := stx[1].getId
  let fact ← realizeGlobalConstNoOverloadWithInfo stx[2]
  let fi ← factInfo fact
  let .const dataName _ := fi.data | throwError "the string argument must be a constant"
  let some (.defnInfo d) := (← getEnv).find? dataName | throwError "`{dataName}` is not a definition"
  -- `D.toList = P.c1 ++ … ++ P.ck` (left-associated, as `D`'s value)
  let listChar := listCharT
  let counter ← IO.mkRef 0
  let (L, hs) ← if countLits d.value ≤ 1 then do
      let (_, L, hs) ← bridgeStr pre counter d.value
      pure (L, hs)
    else do
      let (L, h) ← bridgeR pre 1 d.value (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Char))
      pure (L, mkAppN (mkConst ``flat_top) #[fi.data, L, h])
  let coverT := mkConst ``BerryEsseen.Upper0423.Native.Cover
  let resT := mkApp (mkConst ``Option [Level.zero]) (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) coverT
    (mkApp (mkConst ``List [Level.zero]) listChar))
  let some_ := mkApp2 (mkConst ``Option.some [Level.zero]) (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) coverT
    (mkApp (mkConst ``List [Level.zero]) listChar))
    (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) coverT (mkApp (mkConst ``List [Level.zero]) listChar)
      (mkConst (tName pre 0)) (mkApp (mkConst ``List.nil [Level.zero]) listChar))
  let parseL := mkApp2 (mkConst ``parseCoverL) (mkRawNatLit 64) (mkApp (mkConst ``tokensL) L)
  let hpLty := mkApp3 (mkConst ``Eq [Level.one]) resT parseL some_
  let ms ← addThm (pre ++ `hpL) hpLty (mkApp2 (mkConst ``Eq.refl [Level.one]) resT some_)
  note s!"parse {pre} hpL kernel_ms={ms}"
  -- `parse_bridge hs hpL : parseCoverL 64 (tokensL D.toList) = some (P.t0, [])`
  let hp := mkAppN (mkConst ``parse_bridge) #[fi.data, L, some_, hs, mkConst (pre ++ `hpL)]
  let pf := ofParseApp fi (mkConst (tName pre 0)) hp
  let ty ← inferType pf
  let ms2 ← addThm (pre ++ `parse) ty pf
  note s!"parse {pre} parse kernel_ms={ms2}"
  logInfo m!"{pre}.parse : {ty}"

/-- `bo_leaves P F a b`: the leaves with leaf index `a ≤ k < b` (preorder), one declaration each. -/
syntax (name := boLeavesCmd) "bo_leaves " ident ident num num : command

@[command_elab boLeavesCmd] def elabBoLeaves : CommandElab := fun stx => liftTermElabM do
  let pre := stx[1].getId
  let fact ← realizeGlobalConstNoOverloadWithInfo stx[2]
  let a := stx[3].isNatLit?.get!
  let b := stx[4].isNatLit?.get!
  let fi ← factInfo fact
  let nodes ← walk pre (← rootBounds fi pre)
  let leaves := nodes.filter (·.split?.isNone)
  let t0 ← IO.monoMsNow
  let mut tot := 0
  for k in [a:min b leaves.size] do
    let nd := leaves[k]!
    let ms ← addThm (pre ++ (`leaf).appendIndexAfter nd.idx) (nodeStmt fi pre nd) reflTrue
    tot := tot + ms
    note s!"leaf {pre} k={k} node={nd.idx} kernel_ms={ms}"
  note s!"leaves {pre} {a}..{min b leaves.size} of {leaves.size} kernel_ms={tot} wall_ms={(← IO.monoMsNow) - t0}"

/-- The proof of node `i`'s statement: `P.leaf<i>` or `P.node<i>`. -/
def nodeProof (pre : Name) (nd : Node) : Expr :=
  mkConst (pre ++ (if nd.split?.isSome then (`node).appendIndexAfter nd.idx else (`leaf).appendIndexAfter nd.idx))

/-- `bo_assemble P F`: the split nodes bottom-up (children must exist), then `P.final : lhs = true`. -/
syntax (name := boAssembleCmd) "bo_assemble " ident ident : command

@[command_elab boAssembleCmd] def elabBoAssemble : CommandElab := fun stx => liftTermElabM do
  let pre := stx[1].getId
  let fact ← realizeGlobalConstNoOverloadWithInfo stx[2]
  let fi ← factInfo fact
  let nodes ← walk pre (← rootBounds fi pre)
  let byIdx : Std.HashMap Nat Node := nodes.foldl (fun m nd => m.insert nd.idx nd) {}
  let t0 ← IO.monoMsNow
  let mut tot := 0
  -- reverse preorder: children before parents
  for nd in nodes.reverse do
    let some (axis, m, il, ir) := nd.split? | continue
    let some ndl := byIdx[il]? | throwError "missing node {il}"
    let some ndr := byIdx[ir]? | throwError "missing node {ir}"
    let b := nd.bounds
    let pf := mkAppN (mkConst (splitLemma fi.kind axis))
      #[fi.n, b[0]!, b[1]!, b[2]!, b[3]!, m,
        mkConst (pre ++ (`t).appendIndexAfter il), mkConst (pre ++ (`t).appendIndexAfter ir),
        reflTrue, nodeProof pre ndl, nodeProof pre ndr]
    tot := tot + (← addThm (pre ++ (`node).appendIndexAfter nd.idx) (nodeStmt fi pre nd) pf)
  let root := nodes[0]!
  let pf := mkApp6 (mkConst ``Eq.trans [Level.one]) (mkConst ``Bool) fi.lhs
    (mkAppN (mkConst (accFn fi.kind)) (#[fi.n] ++ root.bounds ++ #[mkConst (tName pre 0)])) boolTrue
    (mkConst (pre ++ `parse)) (nodeProof pre root)
  let ms ← addThm (pre ++ `final) (mkEqTrue fi.lhs) pf
  note s!"assemble {pre} nodes={nodes.size} node_kernel_ms={tot} final_ms={ms} wall_ms={(← IO.monoMsNow) - t0}"

/-- `bo_leaves_nt P F a b`: as `bo_leaves`, through NativeTrust's `proveTrueByKernel` with `opt`
(kernel-reducible copies with small definitions inlined; experimental, for timing comparisons). -/
syntax (name := boLeavesNtCmd) "bo_leaves_nt " ident ident num num : command

@[command_elab boLeavesNtCmd] def elabBoLeavesNt : CommandElab := fun stx => liftTermElabM do
  let pre := stx[1].getId
  let fact ← realizeGlobalConstNoOverloadWithInfo stx[2]
  let a := stx[3].isNatLit?.get!
  let b := stx[4].isNatLit?.get!
  let fi ← factInfo fact
  let nodes ← walk pre (← rootBounds fi pre)
  let leaves := nodes.filter (·.split?.isNone)
  let cfg : NativeTrust.KernelConfig :=
    { ({} : NativeTrust.KernelConfig) with opt := true, native := false, trace := true, accFallback := false, diagnoseFalse := false, maxRecDepth := 1000000 }
  for k in [a:min b leaves.size] do
    let nd := leaves[k]!
    let some (_, e, _) := (nodeStmt fi pre nd).eq? | unreachable!
    let t0 ← IO.monoMsNow
    let r ← NativeTrust.proveTrueByKernel e (pre ++ (`leaf).appendIndexAfter nd.idx) [] cfg
    note s!"leafnt {pre} k={k} node={nd.idx} kernel_ms={r.ms} copies={r.copies.size} wall_ms={(← IO.monoMsNow) - t0}"

end BerryOpt
