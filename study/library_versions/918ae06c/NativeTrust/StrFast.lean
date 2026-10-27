/-!
# Linear-time kernel forms of string construction and decoding

The kernel evaluates strings through their logical definitions:

* a string literal is unfolded to `String.ofList [c₁, …, cₙ]`, whose bytes are
  `(l.flatMap String.utf8EncodeChar).toByteArray`; `List.toByteArray` pushes the bytes one at a
  time, and `Array.push` is `List.concat`, so building the bytes costs time and memory quadratic in
  the length (`strlit/`: 1,000 characters take about 20 s and 4.6 GB);
* `String.toList` decodes the bytes with `ByteArray.utf8Decode?`, which reads the array by index
  (`List` access, linear per read) and pushes each character, again quadratic.

`ofListFast` builds the byte array in one step, and `toListFast` decodes a byte list from its front
with core's one-character decoder on (at most) four bytes at a time. Both are proved equal to the
core functions (`ofList_eq_ofListFast`, `toList_eq_toListFast`), so NativeTrust can use them in
kernel copies and bridge the results back. This module imports nothing beyond `Init`.
-/

namespace NativeTrust

/-- The byte array of a byte list, built in one step. -/
theorem byteArray_mk_toArray (bs : List UInt8) : (⟨bs.toArray⟩ : ByteArray) = bs.toByteArray :=
  ByteArray.ext List.data_toByteArray.symm

/-- `String.ofList` with its byte array built in one step. -/
def ofListFast (l : List Char) : String :=
  String.ofByteArray ⟨(l.flatMap String.utf8EncodeChar).toArray⟩
    (.intro l (byteArray_mk_toArray _))

theorem ofList_eq_ofListFast (l : List Char) : String.ofList l = ofListFast l := by
  rw [← String.toByteArray_inj, String.toByteArray_ofList]
  exact (byteArray_mk_toArray _).symm

theorem ofList_eq_ofListFast' : @String.ofList = @ofListFast :=
  funext ofList_eq_ofListFast

/-- Decode at most `fuel` characters from the front of a byte list: core's one-character decoder
on the first (at most) four bytes, then drop the character's bytes. -/
def decodeAux : Nat → List UInt8 → List Char
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, b :: bs =>
    match ByteArray.utf8DecodeChar? ⟨((b :: bs).take 4).toArray⟩ 0 with
    | some c => c :: decodeAux n ((b :: bs).drop c.utf8Size)
    | none => []

/-- `String.toList` by `decodeAux` over the byte list. -/
def toListFast (s : String) : List Char :=
  decodeAux s.toByteArray.size s.toByteArray.data.toList

theorem decodeAux_cons_of (c : Char) (rest : List UInt8) (n : Nat) :
    decodeAux (n + 1) (String.utf8EncodeChar c ++ rest) = c :: decodeAux n rest := by
  have hlen : (String.utf8EncodeChar c).length = c.utf8Size := String.length_utf8EncodeChar c
  have hpos := c.utf8Size_pos
  have hle := c.utf8Size_le_four
  -- the decoder sees the character's bytes followed by (part of) the rest
  have htake : (String.utf8EncodeChar c ++ rest).take 4 =
      String.utf8EncodeChar c ++ rest.take (4 - c.utf8Size) := by
    rw [List.take_append, List.take_of_length_le (by omega), hlen]
  have hba : (⟨(String.utf8EncodeChar c ++ rest.take (4 - c.utf8Size)).toArray⟩ : ByteArray) =
      (String.utf8EncodeChar c).toByteArray ++ ⟨(rest.take (4 - c.utf8Size)).toArray⟩ := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    show (String.utf8EncodeChar c ++ rest.take (4 - c.utf8Size)) =
      ((String.utf8EncodeChar c).toByteArray.append ⟨(rest.take (4 - c.utf8Size)).toArray⟩).data.toList
    rw [ByteArray.toList_data_append', List.toList_data_toByteArray]
  have hdec : ByteArray.utf8DecodeChar? ⟨((String.utf8EncodeChar c ++ rest).take 4).toArray⟩ 0 =
      some c := by
    rw [htake, hba]
    exact ByteArray.utf8DecodeChar?_utf8EncodeChar_append
  have hdrop : (String.utf8EncodeChar c ++ rest).drop c.utf8Size = rest := List.drop_left' hlen
  match h : String.utf8EncodeChar c with
  | [] => rw [h] at hlen; simp at hlen; omega
  | b :: bs =>
    rw [h] at hdec hdrop
    rw [List.cons_append] at hdec hdrop ⊢
    simp only [decodeAux, hdec, hdrop]

theorem decodeAux_flatMap (l : List Char) (n : Nat)
    (hn : (l.flatMap String.utf8EncodeChar).length ≤ n) :
    decodeAux n (l.flatMap String.utf8EncodeChar) = l := by
  induction l generalizing n with
  | nil => cases n <;> simp [decodeAux]
  | cons c l ih =>
    rw [List.flatMap_cons] at hn ⊢
    have hlen : (String.utf8EncodeChar c).length = c.utf8Size := String.length_utf8EncodeChar c
    have hpos := c.utf8Size_pos
    rw [List.length_append, hlen] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [decodeAux_cons_of, ih m (by omega)]

theorem toListFast_eq (s : String) : toListFast s = s.toList := by
  conv => lhs; rw [← String.ofList_toList (s := s)]
  unfold toListFast
  rw [String.toByteArray_ofList, List.utf8Encode, List.toList_data_toByteArray]
  apply decodeAux_flatMap
  rw [ByteArray.size, List.data_toByteArray, List.size_toArray]
  exact Nat.le_refl _

theorem toList_eq_toListFast : @String.toList = @toListFast :=
  funext fun s => (toListFast_eq s).symm

end NativeTrust
