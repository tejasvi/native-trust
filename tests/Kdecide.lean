import NativeTrust
open NativeTrust
set_option Elab.async false

-- 1. plain kernel evaluation (no copies needed)
theorem t_sum : (List.range 1000).foldl (· + ·) 0 = 499500 := by kdecide
#print axioms t_sum

-- 2. core well-founded recursion that `decide +kernel` cannot evaluate
theorem t_msort : (List.range 300).reverse.mergeSort = List.range 300 := by kdecide
#print axioms t_msort

-- 3. user well-founded recursion with a lexicographic measure
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m+1, 0 => ack m 1
  | m+1, n+1 => ack m (ack (m+1) n)
termination_by m n => (m, n)

theorem t_ack : ack 2 3 = 9 := by kdecide
#print axioms t_ack

-- 4. strings
theorem t_str1 : "hello".length = 5 := by kdecide
theorem t_str2 : "abc" ++ "d" = "abcd" := by kdecide
theorem t_str3 : toString 12345 = "12345" := by kdecide
theorem t_str4 : "a,b,c".splitOn "," = ["a", "b", "c"] := by kdecide
theorem t_str5 : "12345".toNat? = some 12345 := by kdecide

-- 5. arrays
theorem t_arr1 : (Array.range 100).foldl (· + ·) 0 = 4950 := by kdecide
theorem t_arr2 : #[1, 2, 3].map (· * 2) = #[2, 4, 6] := by kdecide
theorem t_arr3 : #[3, 1, 2].qsort (· < ·) = #[1, 2, 3] := by kdecide
theorem t_arr4 : #[5, 2, 9, 1].insertionSort (· < ·) = #[1, 2, 5, 9] := by kdecide

-- 6. fixed-width integers
theorem t_u64 : (123456789 : UInt64) * 987654321 % 1000000007 = 259106859 := by kdecide
