-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

import MettaHyperonFull.Core.Grounding

namespace Metta

/-- Abstract host-language bridge for Rust/Python/Julia/C groundings. -/
structure HostFunction where
  name : String
  contract : Option Atom
  deterministic : Bool
  mayMutateSpace : Bool
  call : List Atom → ReduceResult

/-- Soundness contract for a host grounding, stated as genuine properties of `f.call`. -/
structure HostSoundness (f : HostFunction) : Prop where
  /-- The grounding is defined on every input: it never declares "no reduction". -/
  total : ∀ args, f.call args ≠ ReduceResult.noReduce
  /-- A grounding flagged `deterministic` returns at most one result. -/
  deterministicSingleResult :
    f.deterministic = true → ∀ args rs, f.call args = ReduceResult.ok rs → rs.length ≤ 1

end Metta
