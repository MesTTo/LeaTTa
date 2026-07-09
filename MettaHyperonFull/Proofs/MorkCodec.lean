-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.MorkCodec
Layer: Proofs
Purpose: Round-trip and coreference laws for the logical MORK atom codec model. Successful encoding
  decodes to the source atom, and a variable name has one slot index inside a side table.
Imports: MettaHyperonFull.Proofs.Basic, MettaHyperonFull.Core.MorkCodec
Trusted boundary: none
Main exports: MorkCodec.indexOf?_eq_some_getAt?, MorkCodec.decode_encodeWithSlots_eq,
  MorkCodec.decode_encode_eq, MorkCodec.same_var_same_slot
Open obligations: distinct-slot compaction, concrete NewVar/VarRef byte traces, mutable grounded
  live-value filtering, and query refinement are later layers.
-/
import MettaHyperonFull.Proofs.Basic
import MettaHyperonFull.Core.MorkCodec

namespace Metta

namespace MorkCodec

theorem indexOf?_eq_some_getAt? {x : VarName} {xs : List VarName} {i : Nat}
    (h : indexOf? x xs = some i) :
    getAt? xs i = some x := by
  induction xs generalizing i with
  | nil =>
      simp [indexOf?] at h
  | cons y ys ih =>
      by_cases hxy : x = y
      · subst hxy
        simp [indexOf?] at h
        cases h
        rfl
      · have hbeq : (x == y) = false := by
          simp [BEq.beq, hxy]
        simp [indexOf?, hbeq] at h
        cases hrest : indexOf? x ys with
        | none =>
            simp [hrest] at h
        | some j =>
            simp [hrest] at h
            cases h
            simp [getAt?, ih hrest]

mutual

/-- Successful slot-based encoding of an atom decodes to the same atom. -/
theorem decode_encodeWithSlots_eq :
    ∀ {slots : List VarName} {a : Atom} {code : Code},
      encodeWithSlots slots a = some code →
        decodeWith slots code = some a
  | slots, Atom.sym s, code, h => by
      simp [encodeWithSlots] at h
      rcases h with ⟨_, rfl⟩
      rfl
  | slots, Atom.var x, code, h => by
      simp [encodeWithSlots] at h
      cases hidx : indexOf? x slots with
      | none =>
          simp [hidx] at h
      | some i =>
          simp [hidx] at h
          cases h
          simp [decodeWith, indexOf?_eq_some_getAt? hidx]
  | slots, Atom.gnd g, code, h => by
      simp [encodeWithSlots] at h
      cases h
      rfl
  | slots, Atom.expr xs, code, h => by
      simp [encodeWithSlots] at h
      rcases h with ⟨_, hmatch⟩
      cases hcodes : encodeListWithSlots slots xs with
      | none =>
          simp [hcodes] at hmatch
      | some codes =>
          simp [hcodes] at hmatch
          cases hmatch
          simp [decodeWith, decodeList_encodeListWithSlots_eq hcodes]

/-- Successful slot-based encoding of an atom list decodes to the same atom list. -/
theorem decodeList_encodeListWithSlots_eq :
    ∀ {slots : List VarName} {xs : List Atom} {codes : List Code},
      encodeListWithSlots slots xs = some codes →
        decodeListWith slots codes = some xs
  | _slots, [], codes, h => by
      simp [encodeListWithSlots] at h
      cases h
      rfl
  | slots, x :: xs, codes, h => by
      unfold encodeListWithSlots at h
      cases hhead : encodeWithSlots slots x with
      | none =>
          simp [hhead] at h
      | some code =>
          cases htail : encodeListWithSlots slots xs with
          | none =>
              simp [hhead, htail] at h
          | some codesTail =>
              simp [hhead, htail] at h
              cases h
              have hx : decodeWith slots code = some x :=
                decode_encodeWithSlots_eq hhead
              have hxs : decodeListWith slots codesTail = some xs :=
                decodeList_encodeListWithSlots_eq htail
              simp [decodeListWith, hx, hxs]

end

/-- Successful top-level encoding decodes to the source atom. -/
theorem decode_encode_eq {a : Atom} {encoded : EncodedAtom}
    (h : encode a = some encoded) :
    decode encoded = some a := by
  unfold encode at h
  by_cases hlen : (Atom.vars a).length ≤ maxVars
  · simp [hlen] at h
    cases hcode : encodeWithSlots (Atom.vars a) a with
    | none =>
        simp [hcode] at h
    | some code =>
        simp [hcode] at h
        cases h
        exact decode_encodeWithSlots_eq hcode
  · simp [hlen] at h

/-- A given variable name has a single first slot inside one side table. -/
theorem same_var_same_slot {slots : List VarName} {x : VarName} {i j : Nat}
    (hi : indexOf? x slots = some i) (hj : indexOf? x slots = some j) :
    i = j := by
  rw [hi] at hj
  cases hj
  rfl

end MorkCodec

end Metta
