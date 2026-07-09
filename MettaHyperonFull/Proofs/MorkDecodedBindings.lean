-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.MorkDecodedBindings
Layer: Proofs
Purpose: Separation laws for structured decoded MORK binding rows.
Imports: MettaHyperonFull.Proofs.MorkNamespace, MettaHyperonFull.Core.MorkDecodedBindings
Trusted boundary: none
Main exports: MorkDecodedBindings.decodeVal_query_namespace,
  MorkDecodedBindings.decodeVal_data_namespace, MorkDecodedBindings.data_val_result_separated
Open obligations: rendering structured decoded variables to `VarName` strings is intentionally left
  out of this layer.
-/
import MettaHyperonFull.Proofs.MorkNamespace
import MettaHyperonFull.Core.MorkDecodedBindings

namespace Metta

namespace MorkDecodedBindings

/-- Decoding a value binding in namespace zero preserves the caller variable name. -/
theorem decodeVal_query_namespace {queryVars : List VarName} {resultId idx : Nat}
    {x : VarName} {atom : Atom}
    (h : MorkCodec.getAt? queryVars idx = some x) :
    decodeVal queryVars resultId 0 idx atom =
      some (DecodedBindingRel.val (MorkNamespace.DecodedVar.query x) atom) := by
  simp [decodeVal, MorkNamespace.decodeVar_query_namespace h]

/-- Decoding a value binding in a non-zero namespace yields a data-side structured variable. -/
theorem decodeVal_data_namespace {queryVars : List VarName} {resultId ns idx : Nat}
    {atom : Atom}
    (hns : ns ≠ 0) :
    decodeVal queryVars resultId ns idx atom =
      some (DecodedBindingRel.val (MorkNamespace.DecodedVar.data resultId ns idx) atom) := by
  simp [decodeVal, MorkNamespace.decodeVar_data_namespace hns]

/-- Value bindings whose data-side variables have different result ids cannot be equal. -/
theorem data_val_result_separated {r1 r2 ns1 ns2 idx1 idx2 : Nat} {a b : Atom}
    (h : r1 ≠ r2) :
    DecodedBindingRel.val (MorkNamespace.DecodedVar.data r1 ns1 idx1) a ≠
      DecodedBindingRel.val (MorkNamespace.DecodedVar.data r2 ns2 idx2) b := by
  intro heq
  cases heq
  exact h rfl

/-- Query-side and data-side value bindings cannot be equal. -/
theorem query_val_data_val_ne (x : VarName) (resultId ns idx : Nat) (a b : Atom) :
    DecodedBindingRel.val (MorkNamespace.DecodedVar.query x) a ≠
      DecodedBindingRel.val (MorkNamespace.DecodedVar.data resultId ns idx) b := by
  intro heq
  cases heq

end MorkDecodedBindings

end Metta
