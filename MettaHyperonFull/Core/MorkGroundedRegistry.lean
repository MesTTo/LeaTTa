-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.MorkGroundedRegistry
Layer: Core
Purpose: Pure host-handle registry model for mutable grounded atoms. A stable handle id resolves to
  the current live atom value, which is then turned into the live-value row filter used by MORK query
  results.
Imports: MettaHyperonFull.Core.MorkGroundedFilter
Trusted boundary: none
Main exports: MorkGroundedRegistry.HostHandle, MorkGroundedRegistry.Registry,
  MorkGroundedRegistry.currentValue, MorkGroundedRegistry.liveRef?,
  MorkGroundedRegistry.passesHandle
Open obligations: actual host mutation is outside Lean. This model only states the pure lookup/filter
  contract at the boundary.
-/
import MettaHyperonFull.Core.MorkGroundedFilter

namespace Metta

namespace MorkGroundedRegistry

/-- Stable runtime handle for a mutable grounded atom. -/
structure HostHandle where
  id : Nat
  deriving Repr, BEq, Inhabited

/-- Pure read view of the host registry. -/
structure Registry where
  live : Nat → Option Atom

/-- Current live value for a handle, if the registry knows it. -/
def currentValue (registry : Registry) (handle : HostHandle) : Option Atom :=
  registry.live handle.id

/-- Convert a host handle into the live ref required by the row post-filter. -/
def liveRef? (registry : Registry) (var : VarName) (handle : HostHandle) :
    Option MorkGroundedFilter.LiveRef :=
  (currentValue registry handle).map (fun current => { var, current })

/-- Check whether a row passes the live-value filter induced by one host handle. -/
def passesHandle (registry : Registry) (row : Bindings) (var : VarName) (handle : HostHandle) :
    Bool :=
  match liveRef? registry var handle with
  | some ref => MorkGroundedFilter.passesLiveRef row ref
  | none => false

end MorkGroundedRegistry

end Metta
