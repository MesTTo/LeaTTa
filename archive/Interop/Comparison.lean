-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

import MettaHyperonFull.Runtime.Program

namespace Metta

/-- A runtime comparison checks this Lean runtime against an external Hyperon executable. -/
structure ExternalComparisonCase where
  name : String
  source : String
  expectedAtoms : List Atom
  deriving Repr, Inhabited

/-- Executable Lean-side checker. -/
def runExternalComparisonLean (c : ExternalComparisonCase) : Bool :=
  match Runtime.runProgramString {} c.source with
  | Except.ok r => r.final.output.atoms == c.expectedAtoms
  | _ => false

end Metta
