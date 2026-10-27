import NativeTrust
open NativeTrust
set_option maxRecDepth 100000
set_option Elab.async false

def sumTo (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do s := s + i
  return s
theorem s01 : sumTo 100 = 4950 := by kdecide                                   -- Std.Range for loop
def sumTo2 (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in 0...n do s := s + i
  return s
theorem s02 : sumTo2 100 = 4950 := by kdecide                                  -- polymorphic range
theorem s03 : "abc".toList = ['a', 'b', 'c'] := by kdecide
theorem s04 : String.intercalate ", " ["a", "b"] = "a, b" := by kdecide
theorem s05 : toString [1, 2, 3] = "[1, 2, 3]" := by kdecide
theorem s06 : "abc".foldl (fun n c => n + c.toNat) 0 = 294 := by kdecide
theorem s07 : ("x=12".drop 2).toNat! = 12 := by kdecide
theorem s08 : "hello world".contains 'w' = true := by kdecide
theorem s09 : "a-b".replace "-" "+" = "a+b" := by kdecide
theorem s10 : (Nat.toDigits 2 10) = ['1', '0', '1', '0'] := by kdecide
theorem s11 : Nat.gcd 1071 462 = 21 := by kdecide
theorem s12 : Nat.log2 1000 = 9 := by kdecide
theorem s13 : Nat.sqrt 1000 = 31 := by kdecide
theorem s14 : (List.range 20).foldr (· + ·) 0 = 190 := by kdecide
theorem s15 : ([1, 2, 3].zip [4, 5, 6]).map (fun (a, b) => a * b) = [4, 10, 18] := by kdecide
theorem s16 : [3, 1, 2].max? = some 3 := by kdecide
theorem s17 : ([1, 2, 3, 2, 1].eraseDups) = [1, 2, 3] := by kdecide
theorem s18 : (#[1, 2, 3].toList.reverse) = [3, 2, 1] := by kdecide
theorem s19 : (#[3, 1, 2].toList.mergeSort) = [1, 2, 3] := by kdecide
theorem s20 : (Array.range 10).filter (· % 2 == 0) = #[0, 2, 4, 6, 8] := by kdecide
theorem s21 : (#[1, 2, 3].foldr (· + ·) 0) = 6 := by kdecide
theorem s22 : (#[1, 2, 3, 4].binSearch 3 (· < ·)) = some 3 := by kdecide
theorem s23 : (Int.natAbs (-7)) = 7 ∧ (-7 : Int) / 2 = -4 ∧ (-7 : Int) % 2 = 1 := by kdecide
theorem s24 : ((3 : Fin 5) + 4) = 2 := by kdecide
theorem s25 : (255 : UInt8) + 1 = 0 := by kdecide
theorem s26 : (0xFFFFFFFF : UInt32).toNat = 4294967295 := by kdecide
theorem s27 : (5 : BitVec 8) * 51 = 255 := by kdecide
theorem s28 : (List.range 30).Nodup := by kdecide
theorem s29 : ∀ i < 50, i * i ≠ 2 := by kdecide
theorem s30 : ∃ i < 50, i * i = 49 := by kdecide
theorem s31 : (Std.TreeMap.empty.insert 1 2 |>.insert 3 4 : Std.TreeMap Nat Nat).get? 3 = some 4 := by kdecide
theorem s32 : ((([] : List Nat).insert 1).insert 2).length = 2 := by kdecide
theorem s33 : Char.ofNat 65 = 'A' := by kdecide
theorem s34 : "ABC".map Char.toLower = "abc" := by kdecide


open Lean in
run_cmd Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut ok := #[]
  let mut bad := #[]
  for i in [1:60] do
    let n := Name.mkSimple s!"s{if i < 10 then "0" else ""}{i}"
    if env.contains n then
      let axs ← collectAxioms n
      if axs.contains ``sorryAx then bad := bad.push n else ok := ok.push n
  logInfo m!"passed {ok.size}: {ok.toList}\nfailed {bad.size}: {bad.toList}"