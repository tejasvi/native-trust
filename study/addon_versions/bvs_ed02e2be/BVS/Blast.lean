import Std.Tactic.BVDecide
/-!
# BVS.Blast: a kernel-friendly bit-blaster for `bv_decide` problems

The bit-blaster of `bv_decide` builds its AIG in `Array`s and `HashMap`s. Lean's kernel evaluates
`Array.push`/`Array.get` as list operations and hash maps through `USize` and the opaque `mixHash`,
so evaluating it in the kernel is quadratic with a large constant. This file is a second
bit-blaster, written for kernel evaluation: structural recursion, lists, and a Nat-keyed binary
trie (`NT`) for the cache of input bits.

* Nodes are natural numbers; node `0` is the constant `false`. A literal is `2 * node + neg`
  (`0` = false, `1` = true).
* The state `St` holds the next fresh node, the defining entries of all nodes (newest first), a cache
  of the nodes of input bits, and memo tables of word operations (`mb`) and dividers (`md`), so that
  a repeated operation on the same literal vectors (e.g. `x / y` and `x % y`) is built once. The
  soundness proof (`BVS.Sound.*`) maintains the invariant that cache and memo entries are correct.
* `cnfOf` is the Tseitin encoding of the defining entries; `wfEs` is a linear check, evaluated by
  the kernel, that the entries form a DAG with distinct nodes.
-/
namespace BVS
open Std.Tactic.BVDecide

/-! ## A Nat-keyed binary trie (key `0` = root, `2m+1` = key `m` on the left, `2m+2` on the right) -/

inductive NT (α : Type) where
  | nil
  | node (v : Option α) (l r : NT α)

namespace NT

def get {α : Type} : NT α → Nat → Option α
  | nil, _ => none
  | node v l r, k =>
    match k with
    | 0 => v
    | k + 1 => cond (Nat.beq (k % 2) 0) (get l (k / 2)) (get r (k / 2))

/-- Set the value at key `k` to `f (old value)`; `n` is fuel for the path length (keys below
`2^n - 1` fit; out of fuel the trie is returned unchanged, which is sound for a cache). -/
def upd {α : Type} : Nat → NT α → Nat → (Option α → α) → NT α
  | 0, t, _, _ => t
  | n + 1, nil, k, f =>
    match k with
    | 0 => node (some (f none)) nil nil
    | k + 1 => cond (Nat.beq (k % 2) 0) (node none (upd n nil (k / 2) f) nil)
        (node none nil (upd n nil (k / 2) f))
  | n + 1, node v l r, k, f =>
    match k with
    | 0 => node (some (f v)) l r
    | k + 1 => cond (Nat.beq (k % 2) 0) (node v (upd n l (k / 2) f) r)
        (node v l (upd n r (k / 2) f))

end NT

/-- Association-list lookup. -/
def assoc (r : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (a, k) :: rest => cond (Nat.beq a r) (some k) (assoc r rest)

/-! ## Literals and the construction state -/

/-- Negation of a literal. -/
def neg (l : Nat) : Nat := cond (Nat.beq (l % 2) 0) (l + 1) (l - 1)

/-- A defining entry: an AND gate `k = l ∧ r` (literals), or input bit `i` of variable `v`. -/
inductive Ent where
  | gate (k l r : Nat)
  | atom (k v i : Nat)

structure St where
  /-- next fresh node -/
  n : Nat
  /-- defining entries, newest first -/
  es : List Ent
  /-- input cache: variable `v ↦` the nodes of its bits `0, 1, …` -/
  ha : NT (List Nat)
  /-- memo of word operations: `(operation code, xs, ys, result)` -/
  mb : List (Nat × List Nat × List Nat × List Nat)
  /-- memo of dividers: `(xs, ys, ys = 0, quotient, remainder)` -/
  md : List (List Nat × List Nat × Nat × List Nat × List Nat)

def St.empty : St := ⟨1, [], .nil, [], []⟩

/-! ## Gates -/

/-- AND of two literals, with constant folding (inputs ordered). -/
def mkAnd (st : St) (a b : Nat) : St × Nat :=
  let l := cond (Nat.ble a b) a b
  let r := cond (Nat.ble a b) b a
  cond (Nat.beq l 0) (st, 0) <|
  cond (Nat.beq l 1) (st, r) <|
  cond (Nat.beq l r) (st, l) <|
  cond (Nat.beq (l % 2) 0 && Nat.beq (l + 1) r) (st, 0) <|
  ({ st with n := st.n + 1, es := .gate st.n l r :: st.es }, 2 * st.n)

def mkOr (st : St) (a b : Nat) : St × Nat :=
  match mkAnd st (neg a) (neg b) with
  | (st, o) => (st, neg o)

def mkXor (st : St) (a b : Nat) : St × Nat :=
  match mkAnd st a (neg b) with
  | (st, x) => match mkAnd st (neg a) b with
    | (st, y) => mkOr st x y

def mkXnor (st : St) (a b : Nat) : St × Nat :=
  match mkXor st a b with
  | (st, o) => (st, neg o)

/-- `c ? a : b` -/
def mkMux (st : St) (c a b : Nat) : St × Nat :=
  match mkAnd st c a with
  | (st, x) => match mkAnd st (neg c) b with
    | (st, y) => mkOr st x y

/-! ## Bit vectors: lists of literals, least significant bit first -/

def zeros : Nat → List Nat
  | 0 => []
  | n + 1 => 0 :: zeros n

/-- Bits of the constant `v` (width `w`). -/
def constBits : Nat → Nat → List Nat
  | 0, _ => []
  | w + 1, v => cond (Nat.beq (v % 2) 0) 0 1 :: constBits w (v / 2)

/-- The first `n` elements, padded with `0`. -/
def takeD : Nat → List Nat → List Nat
  | 0, _ => []
  | n + 1, [] => 0 :: takeD n []
  | n + 1, x :: xs => x :: takeD n xs

def zipSt (f : St → Nat → Nat → St × Nat) : St → List Nat → List Nat → St × List Nat
  | st, x :: xs, y :: ys =>
    match f st x y with
    | (st, z) => match zipSt f st xs ys with
      | (st, zs) => (st, z :: zs)
  | st, _, _ => (st, [])

def muxV (st : St) (c : Nat) (xs ys : List Nat) : St × List Nat :=
  zipSt (fun st a b => mkMux st c a b) st xs ys

/-- Majority of three literals (the carry of a full adder). -/
def mkMaj (st : St) (a b c : Nat) : St × Nat :=
  match mkXor st a b with
  | (st, x) => match mkAnd st x c with
    | (st, t1) => match mkAnd st a b with
      | (st, t2) => mkOr st t1 t2

/-- Ripple-carry addition with carry-in `c`; returns the sum bits and the carry out. -/
def addGo : St → List Nat → List Nat → Nat → St × List Nat × Nat
  | st, a :: as, b :: bs, c =>
    match mkXor st a b with
    | (st, x) => match mkXor st x c with
      | (st, s) => match mkAnd st x c with
        | (st, t1) => match mkAnd st a b with
          | (st, t2) => match mkOr st t1 t2 with
            | (st, c') => match addGo st as bs c' with
              | (st, ss, co) => (st, s :: ss, co)
  | st, _, _, c => (st, [], c)

def blastAdd (st : St) (xs ys : List Nat) : St × List Nat :=
  match addGo st xs ys 0 with
  | (st, ss, _) => (st, ss)

/-- The carry chain alone. -/
def carryGo : St → List Nat → List Nat → Nat → St × Nat
  | st, a :: as, b :: bs, c =>
    match mkMaj st a b c with
    | (st, c') => carryGo st as bs c'
  | st, _, _, c => (st, c)

/-- `x <ᵤ y` iff the addition `x + ~~~y + 1` has no carry out. -/
def blastUlt (st : St) (xs ys : List Nat) : St × Nat :=
  match carryGo st xs (ys.map neg) 1 with
  | (st, c) => (st, neg c)

def andAll : St → List Nat → St × Nat
  | st, [] => (st, 1)
  | st, z :: zs => match andAll st zs with
    | (st, r) => mkAnd st z r

def blastEq (st : St) (xs ys : List Nat) : St × Nat :=
  match zipSt mkXnor st xs ys with
  | (st, zs) => andAll st zs

/-- `xs <<< i` (width `xs.length`). -/
def shl (xs : List Nat) (i : Nat) : List Nat := takeD xs.length (zeros i ++ xs)

/-- Shift-and-add multiplication; skips constant-false bits of the right operand. -/
def mulGo (xs : List Nat) : St → List Nat → Nat → List Nat → St × List Nat
  | st, [], _, acc => (st, acc)
  | st, y :: ys, i, acc =>
    cond (Nat.beq y 0) (mulGo xs st ys (i + 1) acc)
      (match blastAdd st acc (shl xs i) with
       | (st, sum) => match muxV st y sum acc with
         | (st, acc') => mulGo xs st ys (i + 1) acc')

def blastMul (st : St) (xs ys : List Nat) : St × List Nat :=
  mulGo xs st ys 0 (zeros xs.length)

/-- Shift in bit `b` at the bottom, dropping the top bit (width `xs.length`). -/
def shiftConcat (xs : List Nat) (b : Nat) : List Nat := takeD xs.length (b :: xs)

/-- One step of restoring division (as `BitVec.divSubtractShift`): returns `(q', r')`. -/
def divStep (st : St) (n d : List Nat) (wn : Nat) (q r : List Nat) : St × List Nat × List Nat :=
  let r' := shiftConcat r (n.getD (wn - 1) 0)
  match addGo st r' (d.map neg) 1 with
  | (st, diff, c) =>
    -- `c = false` iff `r' < d`
    match muxV st c (shiftConcat q 1) (shiftConcat q 0) with
    | (st, q') => match muxV st c diff r' with
      | (st, r'') => (st, q', r'')

def divGo (n d : List Nat) : St → Nat → Nat → List Nat → List Nat → St × List Nat × List Nat
  | st, 0, _, q, r => (st, q, r)
  | st, k + 1, wn, q, r =>
    match divStep st n d wn q r with
    | (st, q', r') => divGo n d st k (wn - 1) q' r'

/-- List equality on literals. -/
def listEq : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && listEq as bs
  | _, _ => false

def findMD (xs ys : List Nat) :
    List (List Nat × List Nat × Nat × List Nat × List Nat) → Option (Nat × List Nat × List Nat)
  | [] => none
  | (a, b, z, q, r) :: rest => cond (listEq a xs && listEq b ys) (some (z, q, r)) (findMD xs ys rest)

/-- The divider of `xs` by `ys` (with the test `ys = 0`), built once per pair of vectors. -/
def divMemo (st : St) (xs ys : List Nat) : St × Nat × List Nat × List Nat :=
  match findMD xs ys st.md with
  | some (z, q, r) => (st, z, q, r)
  | none =>
    match blastEq st ys (zeros xs.length) with
    | (st, z) => match divGo xs ys st xs.length xs.length (zeros xs.length) (zeros xs.length) with
      | (st, q, r) => ({ st with md := (xs, ys, z, q, r) :: st.md }, z, q, r)

def blastUdiv (st : St) (xs ys : List Nat) : St × List Nat :=
  match divMemo st xs ys with
  | (st, z, q, _) => muxV st z (zeros xs.length) q

def blastUmod (st : St) (xs ys : List Nat) : St × List Nat :=
  match divMemo st xs ys with
  | (st, z, _, r) => muxV st z xs r

/-! ## Shifts, rotations, replication -/

/-- `xs <<< k` for a constant `k` (width `xs.length`). -/
def shlC (xs : List Nat) (k : Nat) : List Nat := cond (Nat.ble xs.length k) (zeros xs.length) (shl xs k)

/-- `xs >>> k` (logical) for a constant `k`. -/
def shrC (xs : List Nat) (k : Nat) : List Nat := takeD xs.length (xs.drop k)

/-- The first `n` elements, padded with `f`. -/
def takeF (f : Nat) : Nat → List Nat → List Nat
  | 0, _ => []
  | n + 1, [] => f :: takeF f n []
  | n + 1, x :: xs => x :: takeF f n xs

/-- Arithmetic shift right by a constant `k`: the vacated bits copy the top bit. -/
def sarC (xs : List Nat) (k : Nat) : List Nat := takeF (xs.getD (xs.length - 1) 0) xs.length (xs.drop k)

/-- Barrel shifter: stage `i` shifts by `2^i` when bit `i` of the distance is set. -/
def barrel (sh : List Nat → Nat → List Nat) : St → List Nat → List Nat → Nat → St × List Nat
  | st, acc, [], _ => (st, acc)
  | st, acc, y :: ys, i =>
    match muxV st y (sh acc (2 ^ i)) acc with
    | (st, acc') => barrel sh st acc' ys (i + 1)

/-- Rotate left by `r` (least significant bit first). -/
def rotl (xs : List Nat) (r : Nat) : List Nat :=
  xs.drop (xs.length - r % xs.length) ++ xs.take (xs.length - r % xs.length)

def rotr (xs : List Nat) (r : Nat) : List Nat :=
  xs.drop (r % xs.length) ++ xs.take (r % xs.length)

/-! ## Input bits -/

/-- Fresh nodes for bits `i, i+1, …, i+c-1` of variable `v`. -/
def allocAtoms (v : Nat) : St → Nat → Nat → St × List Nat
  | st, _, 0 => (st, [])
  | st, i, c + 1 =>
    match allocAtoms v { st with n := st.n + 1, es := .atom st.n v i :: st.es } (i + 1) c with
    | (st', ks) => (st', st.n :: ks)

def dbl (ks : List Nat) : List Nat := ks.map (2 * ·)

/-- The literals of bits `0 … w-1` of variable `v`. -/
def blastVar (st : St) (v w : Nat) : St × List Nat :=
  let ks := (st.ha.get v).getD []
  cond (Nat.ble w ks.length) (st, dbl (ks.take w))
    (match allocAtoms v st ks.length (w - ks.length) with
     | (st', ks') => ({ st' with ha := st'.ha.upd 64 v (fun _ => ks ++ ks') }, dbl (ks ++ ks')))

/-! ## Expressions -/

def blastBinRaw (op : BVBinOp) (st : St) (xs ys : List Nat) : St × List Nat :=
  match op with
  | .and => zipSt mkAnd st xs ys
  | .or => zipSt mkOr st xs ys
  | .xor => zipSt mkXor st xs ys
  | .add => blastAdd st xs ys
  | .mul => blastMul st xs ys
  | .udiv => blastUdiv st xs ys
  | .umod => blastUmod st xs ys

def opCode : BVBinOp → Nat
  | .and => 0 | .or => 1 | .xor => 2 | .add => 3 | .mul => 4 | .udiv => 5 | .umod => 6

def findMB (c : Nat) (xs ys : List Nat) : List (Nat × List Nat × List Nat × List Nat) → Option (List Nat)
  | [] => none
  | (o, a, b, z) :: rest => cond (Nat.beq o c && listEq a xs && listEq b ys) (some z) (findMB c xs ys rest)

/-- A word operation, built once per operation and pair of vectors. -/
def blastBin (op : BVBinOp) (st : St) (xs ys : List Nat) : St × List Nat :=
  match findMB (opCode op) xs ys st.mb with
  | some zs => (st, zs)
  | none =>
    match blastBinRaw op st xs ys with
    | (st, zs) => ({ st with mb := (opCode op, xs, ys, zs) :: st.mb }, zs)

/-- The unary operations handled by `blastExpr` (all of them). -/
def unSupported : BVUnOp → Bool
  | .not => true
  | .rotateLeft _ => true
  | .rotateRight _ => true
  | .arithShiftRightConst _ => true
  | .reverse => true
  | .clz => true
  | .cpop => true

/-- The constructors handled by `blastExpr`. -/
def supported : BVExpr w → Bool
  | .var _ => true
  | .const _ => true
  | .extract _ _ e => supported e
  | .bin x _ y => supported x && supported y
  | .un op x => unSupported op && supported x
  | .append x y _ => supported x && supported y
  | .replicate _ x _ => supported x
  | .shiftLeft x y => supported x && supported y
  | .shiftRight x y => supported x && supported y
  | .arithShiftRight x y => supported x && supported y

def unOp (op : BVUnOp) (xs : List Nat) : List Nat :=
  match op with
  | .not => xs.map neg
  | .rotateLeft r => rotl xs r
  | .rotateRight r => rotr xs r
  | .arithShiftRightConst k => sarC xs k
  | .reverse => xs.reverse
  | _ => xs

/-- Count leading zeros, following `BitVec.clzAuxRec`: step `n` is
`if bit n then w - 1 - n else (step n - 1)`, step `0` is `if bit 0 then w - 1 else w`. -/
def clzGo (xs : List Nat) (w : Nat) : Nat → St → St × List Nat
  | 0, st => muxV st (xs.getD 0 0) (constBits w (w - 1)) (constBits w w)
  | n + 1, st =>
    match clzGo xs w n st with
    | (st, r) => muxV st (xs.getD (n + 1) 0) (constBits w (w - 1 - (n + 1))) r

def blastClz (st : St) (xs : List Nat) : St × List Nat := clzGo xs xs.length (xs.length - 1) st

/-- Population count, following `BitVec.cpopNatRec`: add bits `n - 1, …, 0` to the accumulator. -/
def cpopGo (xs : List Nat) (w : Nat) : Nat → St → List Nat → St × List Nat
  | 0, st, acc => (st, acc)
  | n + 1, st, acc =>
    match blastAdd st acc (xs.getD n 0 :: zeros (w - 1)) with
    | (st, acc) => cpopGo xs w n st acc

def blastCpop (st : St) (xs : List Nat) : St × List Nat := cpopGo xs xs.length xs.length st (zeros xs.length)

def blastUn (op : BVUnOp) (st : St) (xs : List Nat) : St × List Nat :=
  match op with
  | .clz => blastClz st xs
  | .cpop => blastCpop st xs
  | op => (st, unOp op xs)

def blastExpr : St → BVExpr w → St × List Nat
  | st, .var v => blastVar st v w
  | st, .const val => (st, constBits w val.toNat)
  | st, .extract start len e =>
    match blastExpr st e with
    | (st, xs) => (st, takeD len (xs.drop start))
  | st, .bin x op y =>
    match blastExpr st x with
    | (st, xs) => match blastExpr st y with
      | (st, ys) => blastBin op st xs ys
  | st, .un op x =>
    match blastExpr st x with
    | (st, xs) => blastUn op st xs
  | st, .append x y _ =>
    match blastExpr st x with
    | (st, xs) => match blastExpr st y with
      | (st, ys) => (st, ys ++ xs)
  | st, .replicate n x _ =>
    match blastExpr st x with
    | (st, xs) => (st, (List.replicate n xs).flatten)
  | st, .shiftLeft x y =>
    match blastExpr st x with
    | (st, xs) => match blastExpr st y with
      | (st, ys) => barrel shlC st xs ys 0
  | st, .shiftRight x y =>
    match blastExpr st x with
    | (st, xs) => match blastExpr st y with
      | (st, ys) => barrel shrC st xs ys 0
  | st, .arithShiftRight x y =>
    match blastExpr st x with
    | (st, xs) => match blastExpr st y with
      | (st, ys) => barrel sarC st xs ys 0

def supportedPred : BVPred → Bool
  | .bin x _ y => supported x && supported y
  | .getLsbD e _ => supported e

def blastPred (st : St) : BVPred → St × Nat
  | .bin x op y =>
    match blastExpr st x with
    | (st, xs) => match blastExpr st y with
      | (st, ys) => match op with
        | .eq => blastEq st xs ys
        | .ult => blastUlt st xs ys
  | .getLsbD e i =>
    match blastExpr st e with
    | (st, xs) => (st, xs.getD i 0)

def supportedBool : BVLogicalExpr → Bool
  | .literal p => supportedPred p
  | .const _ => true
  | .not x => supportedBool x
  | .gate _ x y => supportedBool x && supportedBool y
  | .ite c x y => supportedBool c && supportedBool x && supportedBool y

def gateOf (g : Gate) (st : St) (a b : Nat) : St × Nat :=
  match g with
  | .and => mkAnd st a b
  | .or => mkOr st a b
  | .xor => mkXor st a b
  | .beq => mkXnor st a b

def blastBool : St → BVLogicalExpr → St × Nat
  | st, .literal p => blastPred st p
  | st, .const b => (st, cond b 1 0)
  | st, .not x =>
    match blastBool st x with
    | (st, l) => (st, neg l)
  | st, .gate g x y =>
    match blastBool st x with
    | (st, a) => match blastBool st y with
      | (st, b) => gateOf g st a b
  | st, .ite c x y =>
    match blastBool st c with
    | (st, c) => match blastBool st x with
      | (st, a) => match blastBool st y with
        | (st, b) => mkMux st c a b

/-! ## Well-formedness and the Tseitin encoding -/

/-- Entries newest first: node indices strictly decreasing, at least `1`, below `b`; gate inputs
below the gate. -/
def wfEs : List Ent → Nat → Bool
  | [], _ => true
  | .gate k l r :: es, b =>
    Nat.blt k b && Nat.ble 1 k && Nat.blt (l / 2) k && Nat.blt (r / 2) k && wfEs es k
  | .atom k _ _ :: es, b => Nat.blt k b && Nat.ble 1 k && wfEs es k

/-- A literal as a CNF literal `(variable, polarity)`. -/
def litC (l : Nat) : Nat × Bool := (l / 2, Nat.beq (l % 2) 0)

def gateClauses : List Ent → List (List (Nat × Bool)) → List (List (Nat × Bool))
  | [], acc => acc
  | .gate k l r :: es, acc =>
    gateClauses es ([(k, false), litC l] :: [(k, false), litC r] ::
      [(k, true), litC (neg l), litC (neg r)] :: acc)
  | .atom .. :: es, acc => gateClauses es acc

/-- The CNF: the output literal, `¬ node 0`, and three clauses per gate. -/
def cnfOf (es : List Ent) (out : Nat) : List (List (Nat × Bool)) :=
  [litC out] :: [(0, false)] :: gateClauses es []

end BVS
