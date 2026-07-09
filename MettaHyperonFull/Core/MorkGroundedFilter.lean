-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.MorkGroundedFilter
Layer: Core
Purpose: Mutable-grounded identity and live-value post-filter model for MORK query results. Mutable
  grounded atoms are addressed by stable ids, while query rows are kept only when the captured value
  equals the current live value required by the query.
Imports: MettaHyperonFull.Core.Matching
Trusted boundary: none
Main exports: MorkGroundedFilter.MutableGrounded, MorkGroundedFilter.LiveRef,
  MorkGroundedFilter.passesLiveRefs, MorkGroundedFilter.filterRows
Open obligations: connecting this abstract filter to concrete grounded host handles is a runtime
  integration layer.
-/
import MettaHyperonFull.Core.Matching

namespace Metta

namespace MorkGroundedFilter

/-- Stable identity for a mutable grounded atom. The snapshot is not used for identity. -/
structure MutableGrounded where
  id : Nat
  snapshot : Atom
  deriving Repr, BEq, Inhabited

/-- A live-value check captured through a wildcard variable during byte-level matching. -/
structure LiveRef where
  var : VarName
  current : Atom
  deriving Repr, BEq, Inhabited

/-- A row passes one live-value check when the captured value equals the current value. -/
def passesLiveRef (row : Bindings) (ref : LiveRef) : Bool :=
  match Bindings.lookupVal row ref.var with
  | some captured => captured == ref.current
  | none => false

/-- A row passes all live-value checks. -/
def passesLiveRefs (refs : List LiveRef) (row : Bindings) : Bool :=
  refs.all (fun ref => passesLiveRef row ref)

/-- Keep only rows whose captured values still match the current live values. -/
def filterRows (refs : List LiveRef) (rows : List Bindings) : List Bindings :=
  rows.filter (passesLiveRefs refs)

end MorkGroundedFilter

end Metta
