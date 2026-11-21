/- The patched `finOpTable` of `memofinop-three-lines.diff` equals the judge's original on every string.
   The original is the judge's own compiled constant (import below); the patched one is copied from the diff.
   Copyright 2026 Carlo Perassi. SPDX-License-Identifier: Apache-2.0
   Written with Claude Code (Claude Opus 5.5), for Carlo Perassi. -/
import JudgeFinOp.MemoFinOp

namespace VE

def byteDigit (b : UInt8) : Option Nat :=
  if 48 ≤ b.toNat ∧ b.toNat ≤ 57 then some (b.toNat - 48) else none

def charDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat) else none

/-- the original's parser, spelled out; `orig_unfold` below ties it to the judge's private constant -/
def extractDigitsOrig (s : String) : List Nat := s.toList.filterMap charDigit

/-- the patched parser, as in memofinop-three-lines.diff -/
def extractDigitsPatched (s : String) : List Nat :=
  s.toUTF8.data.toList.filterMap fun b =>
    if 48 ≤ b.toNat ∧ b.toNat ≤ 57 then some (b.toNat - 48) else none

def finOpTablePatched (s : String) (i j : Fin n) : Fin n :=
  let vals := extractDigitsPatched s
  let idx := i.val * n + j.val
  ⟨((vals.drop idx).headD 0) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

theorem toNat_ofNat_lt (m : Nat) (h : m < 256) : (UInt8.ofNat m).toNat = m := by
  simp [UInt8.toNat_ofNat']
  omega

theorem byteDigit_small (m : Nat) (h : m < 256) :
    byteDigit (UInt8.ofNat m) = if 48 ≤ m ∧ m ≤ 57 then some (m - 48) else none := by
  unfold byteDigit
  rw [toNat_ofNat_lt m h]

/-- A byte of a multi-byte encoding is at least 128, so it is no digit. -/
theorem skip_high (m : Nat) (l : List UInt8) (h : 128 ≤ m) (h' : m < 256) :
    (UInt8.ofNat m :: l).filterMap byteDigit = l.filterMap byteDigit := by
  rw [List.filterMap_cons, byteDigit_small m h', if_neg (by omega)]

theorem isDigit_iff (c : Char) : c.isDigit = true ↔ (48 ≤ c.val.toNat ∧ c.val.toNat ≤ 57) := by
  simp [Char.isDigit, UInt32.le_iff_toNat_le]

theorem charDigit_eq (c : Char) :
    charDigit c = if 48 ≤ c.val.toNat ∧ c.val.toNat ≤ 57 then some (c.val.toNat - 48) else none := by
  unfold charDigit
  by_cases hd : c.isDigit = true
  · rw [if_pos hd, if_pos ((isDigit_iff c).1 hd)]
    rfl
  · rw [if_neg hd, if_neg (fun x => hd ((isDigit_iff c).2 x))]

theorem enc_char (c : Char) :
    (String.utf8EncodeChar c).filterMap byteDigit = (charDigit c).toList := by
  by_cases h1 : c.val.toNat ≤ 0x7f
  · -- one byte, the code point itself
    have he : String.utf8EncodeChar c = [UInt8.ofNat c.val.toNat] := by
      unfold String.utf8EncodeChar
      exact if_pos h1
    rw [he, charDigit_eq, List.filterMap_cons, byteDigit_small _ (by omega)]
    by_cases hr : 48 ≤ c.val.toNat ∧ c.val.toNat ≤ 57
    · simp only [if_pos hr]
      rfl
    · simp only [if_neg hr]
      rfl
  · -- several bytes, all at least 128; and the character is no digit
    have hc : charDigit c = none := by
      rw [charDigit_eq, if_neg (by omega)]
    rw [hc]
    unfold String.utf8EncodeChar
    dsimp only
    rw [if_neg h1]
    split
    · rw [skip_high _ _ (by omega) (by omega), skip_high _ _ (by omega) (by omega)]
      rfl
    · split
      · rw [skip_high _ _ (by omega) (by omega), skip_high _ _ (by omega) (by omega),
            skip_high _ _ (by omega) (by omega)]
        rfl
      · rw [skip_high _ _ (by omega) (by omega), skip_high _ _ (by omega) (by omega),
            skip_high _ _ (by omega) (by omega), skip_high _ _ (by omega) (by omega)]
        rfl

theorem chars_flat (l : List Char) :
    (l.flatMap String.utf8EncodeChar).filterMap byteDigit = l.filterMap charDigit := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.flatMap_cons, List.filterMap_append, ih, enc_char]
    cases h : charDigit c <;> simp [h]

theorem bytes_of_string (s : String) :
    s.toUTF8.data.toList = s.toList.flatMap String.utf8EncodeChar := by
  rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList]
  exact List.toList_data_toByteArray

theorem parser_same (s : String) : extractDigitsPatched s = extractDigitsOrig s := by
  show s.toUTF8.data.toList.filterMap byteDigit = s.toList.filterMap charDigit
  rw [bytes_of_string, chars_flat]

theorem headD_drop (l : List Nat) (k d : Nat) : (l.drop k).headD d = l.getD k d := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih => cases k <;> simp_all

/-- The judge's own finOpTable, unfolded: this `rfl` ties `extractDigitsOrig` to its private parser. -/
theorem orig_unfold {n : Nat} (s : String) (i j : Fin n) :
    (MemoFinOp.finOpTable s i j).val = ((extractDigitsOrig s).getD (i.val * n + j.val) 0) % n := rfl

/-- On every string, every n and every i, j: patched and original agree. -/
theorem finOpTable_same {n : Nat} (s : String) (i j : Fin n) :
    MemoFinOp.finOpTable s i j = finOpTablePatched s i j := by
  apply Fin.ext
  rw [orig_unfold]
  show _ = ((extractDigitsPatched s).drop (i.val * n + j.val)).headD 0 % n
  rw [parser_same, headD_drop]

end VE

#print axioms VE.finOpTable_same
#print axioms VE.finOpTablePatched
#check @VE.finOpTable_same

-- kernel differential tests on strings with characters of 1, 2, 3 and 4 UTF-8 bytes
open VE in
example : extractDigitsPatched "a٣b３c𝟘d7é—9" = [7, 9] := by decide
open VE in
example : extractDigitsOrig "a٣b３c𝟘d7é—9" = [7, 9] := by decide
open VE in
example : extractDigitsOrig "[[0, 1], [1, 0]]" = extractDigitsPatched "[[0, 1], [1, 0]]" := by decide
open VE in
example : extractDigitsPatched "日本語 only" = [] := by decide
open VE in
example : extractDigitsPatched "\x30\u0663\uFFFD\x39" = [0, 9] := by decide
open VE in
example : extractDigitsOrig "\x30\u0663\uFFFD\x39" = [0, 9] := by decide
