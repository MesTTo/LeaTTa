-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.MorkGroundedFilter
Layer: Proofs
Purpose: Mutable-grounded identity and live-value post-filter laws for MORK query rows.
Imports: MettaHyperonFull.Proofs.BindingLaws, MettaHyperonFull.Core.MorkGroundedFilter
Trusted boundary: none
Main exports: MorkGroundedFilter.mutable_identity_ignores_snapshot,
  MorkGroundedFilter.passesLiveRefs_nil, MorkGroundedFilter.filterRows_nil,
  MorkGroundedFilter.passesLiveRef_bound_same, MorkGroundedFilter.passesLiveRef_missing
Open obligations: host-handle equality and current-value extraction are outside the pure model.
-/
import MettaHyperonFull.Proofs.BindingLaws
import MettaHyperonFull.Core.MorkGroundedFilter

namespace Metta

namespace MorkGroundedFilter

/-- Mutable grounded identity is the stable id, not the stored snapshot value. -/
theorem mutable_identity_ignores_snapshot (id : Nat) (oldSnapshot newSnapshot : Atom) :
    ({ id := id, snapshot := oldSnapshot } : MutableGrounded).id =
      ({ id := id, snapshot := newSnapshot } : MutableGrounded).id := rfl

/-- With no live refs, every row passes. -/
theorem passesLiveRefs_nil (row : Bindings) :
    passesLiveRefs [] row = true := rfl

/-- With no live refs, filtering preserves all rows. -/
theorem filterRows_nil (rows : List Bindings) :
    filterRows [] rows = rows := by
  simp [filterRows, passesLiveRefs_nil]

/-- A row with the current structurally reflexive value passes the one-ref live filter. -/
theorem passesLiveRef_bound_same (row : Bindings) (var : VarName) (current : Atom)
    (href : Atom.StructurallyReflexive current) :
    passesLiveRef (Bindings.addValRaw row var current) { var, current } = true := by
  unfold Atom.StructurallyReflexive at href
  simp [passesLiveRef, Bindings.lookupVal_addValRaw_self]
  change Atom.beq current current = true
  exact href

/-- A missing captured variable fails the one-ref live filter. -/
theorem passesLiveRef_missing (row : Bindings) (var : VarName) (current : Atom)
    (h : Bindings.lookupVal row var = none) :
    passesLiveRef row { var, current } = false := by
  simp [passesLiveRef, h]

end MorkGroundedFilter

end Metta
