-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

import MettaHyperonFull.Runtime.Parser
import MettaHyperonFull.Runtime.Evaluator

namespace Metta.Runtime
open Metta

structure ProgramResult where
  loaded : State
  final : State
  deriving Repr

/-- Execute a parsed program. Non-bang atoms become KB atoms; bang calls run. -/
def runProgramAtoms (cfg : RuntimeConfig) (atoms : List Atom) : ProgramResult :=
  let loaded := loadProgram State.empty atoms
  { loaded := loaded, final := run cfg loaded }

def runProgramString (cfg : RuntimeConfig) (src : String) : Except String ProgramResult := do
  let atoms ← parseProgram src
  pure (runProgramAtoms cfg atoms)

end Metta.Runtime
