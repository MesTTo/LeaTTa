-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.MorkDecodedBindings
Layer: Core
Purpose: Structured decoded binding rows for MORK query results. Query variables and data-side
  variables remain `MorkNamespace.DecodedVar` values instead of being rendered to strings too early.
Imports: MettaHyperonFull.Core.MorkNamespace
Trusted boundary: none
Main exports: MorkDecodedBindings.DecodedBindingRel, MorkDecodedBindings.DecodedBindings,
  MorkDecodedBindings.decodeVal, MorkDecodedBindings.decodeEq, MorkDecodedBindings.varsOfRel,
  MorkDecodedBindings.vars
Open obligations: string rendering is deliberately outside this layer. A later runtime boundary may
  add an injective renderer if a `VarName`-only API requires it.
-/
import MettaHyperonFull.Core.MorkNamespace

namespace Metta

namespace MorkDecodedBindings

/-- A decoded binding relation whose variable keys have not been flattened to strings. -/
inductive DecodedBindingRel where
  | val : MorkNamespace.DecodedVar → Atom → DecodedBindingRel
  | eq : MorkNamespace.DecodedVar → MorkNamespace.DecodedVar → DecodedBindingRel
  deriving Repr, BEq, Inhabited

abbrev DecodedBindings := List DecodedBindingRel

/-- Decode a value binding key from a MORK query-result namespace/index pair. -/
def decodeVal (queryVars : List VarName) (resultId ns idx : Nat) (atom : Atom) :
    Option DecodedBindingRel :=
  (MorkNamespace.decodeVar queryVars resultId ns idx).map (fun var => DecodedBindingRel.val var atom)

/-- Decode an equality binding key pair from MORK query-result namespace/index pairs. -/
def decodeEq (queryVars : List VarName) (resultId nsA idxA nsB idxB : Nat) :
    Option DecodedBindingRel :=
  match MorkNamespace.decodeVar queryVars resultId nsA idxA,
    MorkNamespace.decodeVar queryVars resultId nsB idxB with
  | some a, some b => some (DecodedBindingRel.eq a b)
  | _, _ => none

/-- Variables mentioned by one decoded binding relation. -/
def varsOfRel : DecodedBindingRel → List MorkNamespace.DecodedVar
  | DecodedBindingRel.val var _ => [var]
  | DecodedBindingRel.eq a b => [a, b]

/-- Variables mentioned by a decoded binding row. -/
def vars (row : DecodedBindings) : List MorkNamespace.DecodedVar :=
  row.flatMap varsOfRel

end MorkDecodedBindings

end Metta
