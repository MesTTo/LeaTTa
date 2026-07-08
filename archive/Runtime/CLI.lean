-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

import MettaHyperonFull.Runtime.Program
import MettaHyperonFull.Core.Pretty

namespace Metta.Runtime
open Metta

def showOutput (s : State) : String := Pretty.atoms s.output.atoms

def runSource (src : String) : String :=
  match runProgramString {} src with
  | Except.error e => "parse/runtime error: " ++ e
  | Except.ok r => showOutput r.final

/-- Read a `.metta` file and run it, returning the pretty-printed output register. -/
def runFile (path : String) : IO String := do
  pure (runSource (← IO.FS.readFile path))

end Metta.Runtime
