module

@[expose] public section

/-!
# LratBits: a kernel-oriented LRAT (RUP) checker over `Nat` bitmasks

Clauses and partial assignments are pairs of natural numbers: bit `v` of the first component is
the positive literal `v`, bit `v` of the second the negative literal `¬v` (for an assignment: `v` is
true, resp. false). Unit propagation then uses only `Nat.land`, `Nat.lor`, `Nat.xor`,
`Nat.shiftLeft` and `Nat.beq`, which Lean's kernel evaluates with GMP.

Clauses are stored in a binary trie over clause ids (`CTrie`), defined by structural recursion.
Every operation is strict in the trie (each insertion forces the path it builds), so the kernel
never accumulates chains of unevaluated insertions.

The certificate is untrusted data: each step carries the clause as two bitmasks and its hints, each
hint with the variable it makes unit (computed by compiled code, checked by the kernel).
`checkBits F acts = true` implies that the clause list `F` is unsatisfiable
(`LratBits.unsat_list_of_checkBits` in `BVS.LratBitsSound`). Only RUP steps are accepted (a RAT
step makes the check fail); deletions are not needed (ignoring them is sound for RUP). The chunk
checker of this package (`BVS.Lrat.Chain`) reuses the clause semantics (`LratBits.ClauseTrue`) and
the bitmask lemmas of these two modules.
-/
namespace LratBits

/-- Clause store: a binary trie over clause ids. Key `0` is the root, key `2m+1` is key `m` of the
left subtree, key `2m+2` is key `m` of the right subtree. -/
inductive CTrie where
  | nil
  | node (v : Option (Nat × Nat)) (l r : CTrie)

namespace CTrie

def get : CTrie → Nat → Option (Nat × Nat)
  | nil, _ => none
  | node v l r, k =>
    match k with
    | 0 => v
    | k + 1 => cond (Nat.beq (k % 2) 0) (get l (k / 2)) (get r (k / 2))

/-- Force a trie to a constructor (kernel evaluation is lazy). -/
@[inline] def force (t : CTrie) (k : CTrie → CTrie) : CTrie :=
  match t with
  | nil => k nil
  | node v l r => k (node v l r)

/-- Insertion with fuel `n` (keys below `2^n - 1` fit; out of fuel the trie is unchanged). -/
def ins : Nat → CTrie → Nat → Nat × Nat → CTrie
  | 0, t, _, _ => t
  | n + 1, nil, k, c =>
    match k with
    | 0 => node (some c) nil nil
    | k + 1 => cond (Nat.beq (k % 2) 0)
        (force (ins n nil (k / 2) c) fun l' => node none l' nil)
        (force (ins n nil (k / 2) c) fun r' => node none nil r')
  | n + 1, node v l r, k, c =>
    match k with
    | 0 => node (some c) l r
    | k + 1 => cond (Nat.beq (k % 2) 0)
        (force (ins n l (k / 2) c) fun l' => node v l' r)
        (force (ins n r (k / 2) c) fun r' => node v l r')

end CTrie

/-- Bitmasks of a clause given as a list of literals `(atom, polarity)`. -/
def litsBits : List (Nat × Bool) → Nat → Nat → Nat × Nat
  | [], cp, cn => (cp, cn)
  | (v, b) :: l, cp, cn =>
    cond b (litsBits l (cp ||| (1 <<< v)) cn) (litsBits l cp (cn ||| (1 <<< v)))

/-- The trie holding clause `i + j` at key `i + j` for the `j`-th clause of the list. -/
def initTrie : List (List (Nat × Bool)) → Nat → CTrie → CTrie
  | [], _, t => t
  | c :: cs, i, t => CTrie.force (CTrie.ins 64 t i (litsBits c 0 0)) fun t' => initTrie cs (i + 1) t'

/-- Outcome of one hint clause under a partial assignment. -/
inductive Step where
  | conflict
  | unit (pa na : Nat)
  | skip

/-- One hint clause `(cp, cn)` under the partial assignment `(pa, na)` (bit `v` of `pa`: `v` is
true; of `na`: `v` is false): a conflict (every literal false), a unit (all literals false but one
unassigned literal, which is then assigned), or skip (satisfied, or not a unit). The certificate
names the unit variable `u` (untrusted); the step only checks that the unassigned literals are
exactly `u` (`Nat.log2` would be evaluated by unfolding its definition, bit by bit). -/
def step (cp cn pa na u : Nat) : Step :=
  cond (Nat.beq ((cp &&& pa) ||| (cn &&& na)) 0)
    (let a := pa ||| na
     let up := cp ^^^ (cp &&& a)
     let un := cn ^^^ (cn &&& a)
     cond (Nat.beq up 0)
       (cond (Nat.beq un 0) .conflict
         (cond (Nat.beq un (1 <<< u)) (.unit pa (na ||| un)) .skip))
       (cond (Nat.beq un 0)
         (cond (Nat.beq up (1 <<< u)) (.unit (pa ||| up) na) .skip)
         .skip))
    .skip

/-- Unit propagation along the hints `(clause id, unit variable)`; `true` = a conflict was reached.
A missing hint fails. -/
def prop (t : CTrie) : Nat → Nat → List (Nat × Nat) → Bool
  | _, _, [] => false
  | pa, na, (h, u) :: hs =>
    match t.get h with
    | none => false
    | some (cp, cn) =>
      match step cp cn pa na u with
      | .conflict => true
      | .unit pa' na' => prop t pa' na' hs
      | .skip => prop t pa na hs

/-- RUP check of the clause `(cp, cn)`: a tautology, or propagation from its negation conflicts. -/
def rupOk (t : CTrie) (cp cn : Nat) (hints : List (Nat × Nat)) : Bool :=
  cond (Nat.beq (cp &&& cn) 0) (prop t cn cp hints) true

/-- A certificate step. -/
inductive BAct where
  /-- Add clause `(cp, cn)` with id `id`, justified by RUP along `hints`. The empty clause
  (`cp = cn = 0`) ends the check. -/
  | rup (id cp cn : Nat) (hints : List (Nat × Nat))
  /-- A step this checker does not support (makes the check fail). -/
  | unsupported

/-- Result of a chunk of steps: the final verdict, or the clause store to continue with. -/
inductive Res where
  | done (b : Bool)
  | cont (t : CTrie)

def runChunk : CTrie → List BAct → Res
  | t, [] => .cont t
  | t, .rup id cp cn hints :: as =>
    cond (rupOk t cp cn hints)
      (cond (Nat.beq (cp ||| cn) 0) (.done true)
        (match CTrie.ins 64 t id (cp, cn) with
         | .nil => runChunk .nil as
         | .node v l r => runChunk (.node v l r) as))
      (.done false)
  | _, .unsupported :: _ => .done false

def runAll : CTrie → List (List BAct) → Bool
  | _, [] => false
  | t, c :: cs =>
    match runChunk t c with
    | .done b => b
    | .cont t' => runAll t' cs

/-- The checker: clause list `F` (clause ids `1, 2, …` in order) and the certificate in chunks. -/
def checkBits (F : List (List (Nat × Bool))) (acts : List (List BAct)) : Bool :=
  runAll (initTrie F 1 .nil) acts

end LratBits
