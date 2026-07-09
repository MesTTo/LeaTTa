-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.MorkCompactCodec
Layer: Proofs
Purpose: Checked compact NewVar/VarRef traces for the MORK codec model.
Imports: MettaHyperonFull.Proofs.MorkCodec, MettaHyperonFull.Core.MorkCompactCodec
Trusted boundary: none
Main exports: MorkCompactCodec.encode_single_var, MorkCompactCodec.decode_single_var,
  MorkCompactCodec.encode_repeated_var_trace, MorkCompactCodec.decode_repeated_var_trace
Open obligations: a general decode-after-encode theorem for the compact trace needs prefix-extension
  lemmas over threaded side tables. The logical codec already has the general round-trip theorem.
-/
import MettaHyperonFull.Proofs.MorkCodec
import MettaHyperonFull.Core.MorkCompactCodec

namespace Metta

namespace MorkCompactCodec

/-- `small` is a prefix of `large`. -/
def Prefix (small large : List VarName) : Prop :=
  ∃ suffix, large = small ++ suffix

namespace Prefix

theorem refl (xs : List VarName) : Prefix xs xs := by
  exists []
  simp

theorem trans {a b c : List VarName} (hab : Prefix a b) (hbc : Prefix b c) :
    Prefix a c := by
  rcases hab with ⟨ab, rfl⟩
  rcases hbc with ⟨bc, rfl⟩
  exists ab ++ bc
  simp [List.append_assoc]

end Prefix

theorem getAt?_append_of_getAt? {α : Type} {xs ys : List α} {i : Nat} {x : α}
    (h : MorkCodec.getAt? xs i = some x) :
    MorkCodec.getAt? (xs ++ ys) i = some x := by
  induction xs generalizing i with
  | nil =>
      simp [MorkCodec.getAt?] at h
  | cons y xs ih =>
      cases i with
      | zero =>
          simp [MorkCodec.getAt?] at h ⊢
          exact h
      | succ i =>
          simp [MorkCodec.getAt?] at h ⊢
          exact ih h

theorem getAt?_prefix_of_getAt? {small large : List VarName} {i : Nat} {x : VarName}
    (hprefix : Prefix small large) (h : MorkCodec.getAt? small i = some x) :
    MorkCodec.getAt? large i = some x := by
  rcases hprefix with ⟨suffix, rfl⟩
  exact getAt?_append_of_getAt? h

theorem getAt?_append_singleton_length (xs : List VarName) (x : VarName) (suffix : List VarName) :
    MorkCodec.getAt? ((xs ++ [x]) ++ suffix) xs.length = some x := by
  induction xs with
  | nil =>
      rfl
  | cons y xs ih =>
      simp [MorkCodec.getAt?]
      simpa [List.append_assoc] using ih

mutual

/-- Encoding only extends the side table. -/
theorem encodeAt_prefix :
    ∀ {seen : List VarName} {a : Atom} {code : Code} {seen' : List VarName},
      encodeAt seen a = some (code, seen') → Prefix seen seen'
  | seen, Atom.sym _s, _code, _seen', h => by
      simp [encodeAt] at h
      rcases h with ⟨_, _hcode, hseen⟩
      cases hseen
      exact Prefix.refl seen
  | seen, Atom.var x, _code, _seen', h => by
      simp [encodeAt] at h
      cases hidx : MorkCodec.indexOf? x seen with
      | some _ =>
          simp [hidx] at h
          rcases h with ⟨_hcode, hseen⟩
          cases hseen
          exact Prefix.refl seen
      | none =>
          simp [hidx] at h
          rcases h with ⟨_, _hcode, hseen⟩
          cases hseen
          exists [x]
  | seen, Atom.gnd _g, _code, _seen', h => by
      simp [encodeAt] at h
      rcases h with ⟨_hcode, hseen⟩
      cases hseen
      exact Prefix.refl seen
  | seen, Atom.expr xs, _code, _seen', h => by
      simp [encodeAt] at h
      rcases h with ⟨_, hmatch⟩
      cases henc : encodeListAt seen xs with
      | none =>
          simp [henc] at hmatch
      | some p =>
          rcases p with ⟨codes, seen''⟩
          simp [henc] at hmatch
          rcases hmatch with ⟨_hcode, hseen⟩
          cases hseen
          exact encodeListAt_prefix henc

/-- List encoding only extends the side table. -/
theorem encodeListAt_prefix :
    ∀ {seen : List VarName} {xs : List Atom} {codes : List Code} {seen' : List VarName},
      encodeListAt seen xs = some (codes, seen') → Prefix seen seen'
  | seen, [], _codes, _seen', h => by
      simp [encodeListAt] at h
      rcases h with ⟨_hcodes, hseen⟩
      cases hseen
      exact Prefix.refl seen
  | seen, x :: xs, _codes, _seen', h => by
      unfold encodeListAt at h
      cases hhead : encodeAt seen x with
      | none =>
          simp [hhead] at h
      | some hp =>
          rcases hp with ⟨code, seen1⟩
          cases htail : encodeListAt seen1 xs with
          | none =>
              simp [hhead, htail] at h
          | some tp =>
              rcases tp with ⟨codesTail, seen2⟩
              simp [hhead, htail] at h
              rcases h with ⟨_hcodes, hseen⟩
              cases hseen
              exact Prefix.trans (encodeAt_prefix hhead) (encodeListAt_prefix htail)

end

mutual

/-- Successful compact encoding decodes to the source atom under any final side-table extension. -/
theorem decode_encodeAt_eq :
    ∀ {seen : List VarName} {a : Atom} {code : Code} {seen' final : List VarName},
      encodeAt seen a = some (code, seen') →
        Prefix seen' final →
          decodeAt final seen.length code = some (a, seen'.length)
  | seen, Atom.sym _s, _code, _seen', _final, h, _hprefix => by
      simp [encodeAt] at h
      rcases h with ⟨_, hcode, hseen⟩
      cases hcode
      cases hseen
      rfl
  | seen, Atom.var x, _code, _seen', final, h, hprefix => by
      simp [encodeAt] at h
      cases hidx : MorkCodec.indexOf? x seen with
      | some i =>
          simp [hidx] at h
          rcases h with ⟨hcode, hseen⟩
          cases hcode
          cases hseen
          have hseen : MorkCodec.getAt? seen i = some x :=
            MorkCodec.indexOf?_eq_some_getAt? hidx
          have hfinal : MorkCodec.getAt? final i = some x :=
            getAt?_prefix_of_getAt? hprefix hseen
          simp [decodeAt, hfinal]
      | none =>
          simp [hidx] at h
          rcases h with ⟨_, hcode, hseen⟩
          cases hcode
          cases hseen
          rcases hprefix with ⟨suffix, rfl⟩
          have hget : MorkCodec.getAt? (seen ++ x :: suffix) seen.length = some x := by
            simpa [List.append_assoc] using getAt?_append_singleton_length seen x suffix
          simp [decodeAt, hget]
  | seen, Atom.gnd _g, _code, _seen', _final, h, _hprefix => by
      simp [encodeAt] at h
      rcases h with ⟨hcode, hseen⟩
      cases hcode
      cases hseen
      rfl
  | seen, Atom.expr xs, _code, _seen', final, h, hprefix => by
      simp [encodeAt] at h
      rcases h with ⟨_, hmatch⟩
      cases henc : encodeListAt seen xs with
      | none =>
          simp [henc] at hmatch
      | some p =>
          rcases p with ⟨codes, seen''⟩
          simp [henc] at hmatch
          rcases hmatch with ⟨hcode, hseen⟩
          cases hcode
          cases hseen
          simp [decodeAt, decodeList_encodeListAt_eq henc hprefix]

/-- Successful compact list encoding decodes to the source atom list under any final side-table
    extension. -/
theorem decodeList_encodeListAt_eq :
    ∀ {seen : List VarName} {xs : List Atom} {codes : List Code} {seen' final : List VarName},
      encodeListAt seen xs = some (codes, seen') →
        Prefix seen' final →
          decodeListAt final seen.length codes = some (xs, seen'.length)
  | seen, [], _codes, _seen', _final, h, _hprefix => by
      simp [encodeListAt] at h
      rcases h with ⟨hcodes, hseen⟩
      cases hcodes
      cases hseen
      rfl
  | seen, x :: xs, _codes, _seen', final, h, hprefix => by
      unfold encodeListAt at h
      cases hhead : encodeAt seen x with
      | none =>
          simp [hhead] at h
      | some hp =>
          rcases hp with ⟨code, seen1⟩
          cases htail : encodeListAt seen1 xs with
          | none =>
              simp [hhead, htail] at h
          | some tp =>
              rcases tp with ⟨codesTail, seen2⟩
              simp [hhead, htail] at h
              rcases h with ⟨hcodes, hseen⟩
              cases hcodes
              have htailPrefix : Prefix seen1 seen2 := encodeListAt_prefix htail
              have hprefixSeen2 : Prefix seen2 final := by
                cases hseen
                exact hprefix
              have hheadFinal : Prefix seen1 final := Prefix.trans htailPrefix hprefixSeen2
              have hx : decodeAt final seen.length code = some (x, seen1.length) :=
                decode_encodeAt_eq hhead hheadFinal
              have hxs : decodeListAt final seen1.length codesTail = some (xs, seen2.length) :=
                decodeList_encodeListAt_eq htail hprefixSeen2
              simp [decodeListAt, hx, hxs, hseen]

end

/-- Successful top-level compact encoding decodes to the source atom. -/
theorem decode_encode_eq {a : Atom} {encoded : EncodedAtom}
    (h : encode a = some encoded) :
    decode encoded = some a := by
  unfold encode at h
  cases henc : encodeAt [] a with
  | none =>
      simp [henc] at h
  | some p =>
      rcases p with ⟨code, vars⟩
      simp [henc] at h
      cases h
      simp [decode]
      have hround : decodeAt vars 0 code = some (a, vars.length) :=
        decode_encodeAt_eq henc (Prefix.refl vars)
      rw [hround]

/-- A first variable occurrence emits `newVar` and creates slot zero. -/
theorem encode_single_var (x : VarName) :
    encode (Atom.var x) = some { code := Code.newVar, vars := [x] } := by
  rfl

/-- A single-variable compact trace decodes to the original variable. -/
theorem decode_single_var (x : VarName) :
    decode { code := Code.newVar, vars := [x] } = some (Atom.var x) := by
  rfl

/-- A repeated variable emits `newVar` followed by `varRef 0`. -/
theorem encode_repeated_var_trace (x : VarName) :
    encode (Atom.expr [Atom.var x, Atom.var x]) =
      some { code := Code.expr [Code.newVar, Code.varRef 0], vars := [x] } := by
  simp [encode, encodeAt, encodeListAt, MorkCodec.indexOf?, MorkCodec.maxField, MorkCodec.maxVars]

/-- The repeated-variable compact trace decodes with source coreference preserved. -/
theorem decode_repeated_var_trace (x : VarName) :
    decode { code := Code.expr [Code.newVar, Code.varRef 0], vars := [x] } =
      some (Atom.expr [Atom.var x, Atom.var x]) := by
  rfl

/-- Two first occurrences followed by a repeated first variable use slots zero and one. -/
example :
    encode (Atom.expr [Atom.var "x", Atom.var "y", Atom.var "x"]) =
      some { code := Code.expr [Code.newVar, Code.newVar, Code.varRef 0], vars := ["x", "y"] } := by
  simp [encode, encodeAt, encodeListAt, MorkCodec.indexOf?, MorkCodec.maxField, MorkCodec.maxVars]

end MorkCompactCodec

end Metta
