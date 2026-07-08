-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

import MettaHyperonFull.Core.Space

namespace Metta

/-- Abstract distributed atomspace address. -/
structure RemoteAddr where
  scheme : String
  endpoint : String
  deriving Repr, BEq, Inhabited

/-- Interface for a distributed Atomspace / DAS backend. -/
structure DistributedSpace where
  localSpace : Space
  remotes : List RemoteAddr
  fetch : RemoteAddr → Atom → List Atom
  push : RemoteAddr → Atom → Bool

/-- Local-only implementation used by the Lean runtime. -/
def localDistributed (s : Space) : DistributedSpace :=
  ⟨s, [], (fun _ _ => []), (fun _ _ => false)⟩

end Metta
