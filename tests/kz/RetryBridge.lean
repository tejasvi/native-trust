import NativeTrust

/-! The fuel route's retry after a rejected bridge (Zag pattern). `mkCtx`'s copy is rejected (the
copied `Valid` occurs in its binder type), so on the first attempt `ctx` gets a copy equal to the
original under another name, and so does the matcher of `t`, whose type mentions `ctx`
(`Option (Val ctx)`). The kernel evaluates the copy (`t…eval` is declared), but the congruence
bridge abstracts `ctx` inside the matcher's fixed type and is ill-typed, and `rfl` cannot relate
`WellFounded.fix` to its fuel copy: the first attempt fails at the bridge. The retry keeps unchanged
originals (`skipUnchanged`) and must not collide with the first attempt's `t…eval`. -/

set_option Elab.async false

/-- Well-founded recursion with a lexicographic measure (compiled to `WellFounded.fix`). -/
def wsum : List Nat → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => wsum xs (acc + x)
termination_by l acc => (l.length, acc)

def Valid (l : List Nat) : Prop := wsum l 0 < 1000

structure Ctx where
  blocks : List Nat

def mkCtx (l : List Nat) (_h : Valid l) : Ctx := ⟨l⟩

theorem ctxValid : Valid [1, 2, 3] := by simp [Valid, wsum]

def ctx : Ctx := mkCtx [1, 2, 3] ctxValid

def Val (c : Ctx) : Type := Fin (c.blocks.length + 1)

/-- Evaluates `wsum`; no proof about `wsum` in the body, so its first copy is accepted. -/
def pick (c : Ctx) : Option (Val c) :=
  if wsum c.blocks 0 = 6 then some (Fin.last _) else none

theorem t : (match pick ctx with | some v => v.val | none => 0) = 3 := by native_decide

trust_check t (config := { trace := true })
#print axioms t.kernel
