-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.MorkGroundedRegistry
Layer: Proofs
Purpose: Boundary laws connecting mutable grounded host handles to the MORK live-value row filter.
Imports: MettaHyperonFull.Proofs.MorkGroundedFilter, MettaHyperonFull.Core.MorkGroundedRegistry
Trusted boundary: none
Main exports: MorkGroundedRegistry.liveRef?_of_currentValue,
  MorkGroundedRegistry.passesHandle_bound_same, MorkGroundedRegistry.passesHandle_missing_handle
Open obligations: concrete host mutation remains outside Lean.
-/
import MettaHyperonFull.Proofs.MorkGroundedFilter
import MettaHyperonFull.Core.MorkGroundedRegistry

namespace Metta

namespace MorkGroundedRegistry

/-- A known host handle produces the corresponding live ref. -/
theorem liveRef?_of_currentValue {registry : Registry} {var : VarName} {handle : HostHandle}
    {current : Atom}
    (h : currentValue registry handle = some current) :
    liveRef? registry var handle = some { var, current } := by
  simp [liveRef?, h]

/-- A row that captures the current live value passes the handle-induced filter. -/
theorem passesHandle_bound_same {registry : Registry} {row : Bindings} {var : VarName}
    {handle : HostHandle} {current : Atom}
    (hcur : currentValue registry handle = some current)
    (href : Atom.StructurallyReflexive current) :
    passesHandle registry (Bindings.addValRaw row var current) var handle = true := by
  simp [passesHandle, liveRef?_of_currentValue hcur,
    MorkGroundedFilter.passesLiveRef_bound_same row var current href]

/-- A missing host handle fails the handle-induced live filter. -/
theorem passesHandle_missing_handle {registry : Registry} {row : Bindings} {var : VarName}
    {handle : HostHandle}
    (hcur : currentValue registry handle = none) :
    passesHandle registry row var handle = false := by
  simp [passesHandle, liveRef?, hcur]

end MorkGroundedRegistry

end Metta
