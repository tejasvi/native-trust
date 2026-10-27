import NativeTrust
open NativeTrust
set_option Elab.async false

-- false proposition: refused by the compiled-code oracle
example : (List.range 10).length = 11 := by kdecide

-- `while` loop: a `partial` function, no kernel proof can exist
def countDown (n : Nat) : Nat := Id.run do
  let mut i := n
  let mut c := 0
  while i > 0 do
    i := i - 1
    c := c + 1
  return c
example : countDown 5 = 5 := by kdecide

-- the platform word size: true on this 64-bit machine, false on a 32-bit one, so the case split over the
-- word size refuses it (hash maps with `Nat` keys convert: `tests/kz/PlatformCases.lean`)
example : USize.size = 18446744073709551616 := by kdecide

-- compiled code that disagrees with the logical definition
def fImpl (_ : Nat) : Bool := true
@[implemented_by fImpl] def f (_ : Nat) : Bool := false
theorem f_native : f 0 = true := by native_decide
example : f 0 = true := by kdecide
