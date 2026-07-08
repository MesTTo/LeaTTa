-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull
Layer: Library root
Purpose: The root of the MeTTa / OpenCog Hyperon formalization in Lean 4. It aggregates the faithful
  core: the object-language foundation under `Core`, the text-to-atoms parser under `Runtime`, the
  minimal MeTTa interpreter (the assembly language of MeTTa) under `Minimal.Interpreter`, and the
  standard library written in MeTTa over those instructions under `Minimal.Stdlib`. The stdlib is
  the validated artifact: it agrees with Hyperon's own oracle test_stdlib.metta. The `Operational.*`
  specification library has its own `lean_lib` target and is not imported here. Earlier exploratory
  models live under archive/ and are not built.
Imports: the MettaHyperonFull.Core, MettaHyperonFull.Runtime, and MettaHyperonFull.Minimal modules
Trusted boundary: none
Main exports: (aggregator; re-exports the library)
Open obligations: none
-/

-- Faithful foundation: the object language the assembly is built on.
import MettaHyperonFull.Core.Atom
import MettaHyperonFull.Core.Pretty
import MettaHyperonFull.Core.Result
import MettaHyperonFull.Core.Bindings
import MettaHyperonFull.Core.Substitution
import MettaHyperonFull.Core.Alpha
import MettaHyperonFull.Core.FreeVars
import MettaHyperonFull.Core.Unification
import MettaHyperonFull.Core.Matching
import MettaHyperonFull.Core.Space
import MettaHyperonFull.Core.Types
import MettaHyperonFull.Core.Grounding
import MettaHyperonFull.Core.Builtins

-- Parser: text to atoms.
import MettaHyperonFull.Runtime.Parser

-- The faithful core: minimal MeTTa interpreter (assembly) plus the stdlib written over it.
import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Minimal.Stdlib

-- `Operational.*` is its own verified `lean_lib «Operational»` target; see the header above.
