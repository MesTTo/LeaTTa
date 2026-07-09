-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.MorkNamespace
Layer: Proofs
Purpose: Namespace-separation laws for MORK query-result variables. Query namespace zero preserves
  caller variable names, data namespaces are distinct from query variables, and different result ids
  cannot alias.
Imports: MettaHyperonFull.Proofs.MorkCodec, MettaHyperonFull.Core.MorkNamespace
Trusted boundary: none
Main exports: MorkNamespace.decodeVar_query_namespace,
  MorkNamespace.decodeVar_data_namespace, MorkNamespace.query_data_ne,
  MorkNamespace.data_resultId_injective, MorkNamespace.data_result_separated
Open obligations: injective string rendering and the connection to decoded binding rows are later
  layers.
-/
import MettaHyperonFull.Proofs.MorkCodec
import MettaHyperonFull.Core.MorkNamespace

namespace Metta

namespace MorkNamespace

/-- Namespace zero preserves the caller's variable name. -/
theorem decodeVar_query_namespace {queryVars : List VarName} {resultId idx : Nat} {x : VarName}
    (h : MorkCodec.getAt? queryVars idx = some x) :
    decodeVar queryVars resultId 0 idx = some (DecodedVar.query x) := by
  simp [decodeVar, h]

/-- Non-zero namespaces decode to data-side variables stamped by the result id. -/
theorem decodeVar_data_namespace {queryVars : List VarName} {resultId ns idx : Nat}
    (hns : ns ≠ 0) :
    decodeVar queryVars resultId ns idx = some (DecodedVar.data resultId ns idx) := by
  have hbeq : (ns == 0) = false := by
    simp [BEq.beq, hns]
  simp [decodeVar, hbeq]

/-- Query variables and data-side variables are disjoint before string rendering. -/
theorem query_data_ne (x : VarName) (resultId ns idx : Nat) :
    DecodedVar.query x ≠ DecodedVar.data resultId ns idx := by
  intro h
  cases h

/-- Equality of data-side variables preserves the result id. -/
theorem data_resultId_injective {r1 r2 ns1 ns2 idx1 idx2 : Nat}
    (h : DecodedVar.data r1 ns1 idx1 = DecodedVar.data r2 ns2 idx2) :
    r1 = r2 := by
  cases h
  rfl

/-- Data-side variables decoded from different query results cannot alias. -/
theorem data_result_separated {r1 r2 ns1 ns2 idx1 idx2 : Nat}
    (h : r1 ≠ r2) :
    DecodedVar.data r1 ns1 idx1 ≠ DecodedVar.data r2 ns2 idx2 := by
  intro heq
  exact h (data_resultId_injective heq)

end MorkNamespace

end Metta
