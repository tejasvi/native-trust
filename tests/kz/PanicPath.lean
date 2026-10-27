import NativeTrust

/-! A panic path is not a blocker: `get!` builds its panic message with C string primitives, but
`panicCore msg` is `default` in the logic and the kernel never evaluates `msg`. -/

def sumGet (l : List Nat) : Nat := (List.range l.length).foldl (fun acc i => acc + l[i]!) 0

theorem sg : sumGet [1, 2, 3, 4] = 10 := by native_decide

#kernel_blockers sg
trust_check sg (config := { trace := true })
