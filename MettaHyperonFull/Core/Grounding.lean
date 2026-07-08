-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.Grounding
Layer: Core
Purpose: The contract for grounded symbols and the table that holds them. A grounding pairs a symbol
  name with its argument mode (evaluate or quote), an optional declared type signature, and the
  reduction that maps argument atoms to a `ReduceResult`. Provides table lookup and the dispatch that
  runs a grounded symbol if present.
Imports: MettaHyperonFull.Core.Types
Trusted boundary: none
Main exports: GroundMode, Grounding, GroundingTable, GroundingTable.lookup, callGrounded
Open obligations: none
-/
import MettaHyperonFull.Core.Types

namespace Metta

/-- Grounding modes: evaluate arguments first, or quote them literally. -/
inductive GroundMode where
  | evalArgs | quoteArgs
  deriving Repr, BEq, Inhabited

/-- Contract for an external or built-in grounded symbol. -/
structure Grounding where
  /-- The grounded symbol's name: the head it is dispatched on (e.g. `"+"`, `"superpose"`). -/
  name : String
  /-- Whether the arguments are evaluated before the implementation runs, or passed quoted. -/
  mode : GroundMode
  /-- Optional declared type signature (an arrow atom), for type-directed evaluation. -/
  typeSig : Option Atom
  /-- The reduction itself: maps the (possibly evaluated) argument atoms to a `ReduceResult`. -/
  impl : List Atom → ReduceResult

/-- The grounding table: all grounded symbols available to the interpreter. -/
abbrev GroundingTable := List Grounding

namespace GroundingTable

def lookup (g : GroundingTable) (name : String) : Option Grounding :=
  g.find? (fun f => f.name == name)

end GroundingTable

/-- Execute a grounded symbol if it is in the table. -/
def callGrounded (gt : GroundingTable) (name : String) (args : List Atom) : ReduceResult :=
  match GroundingTable.lookup gt name with
  | none => ReduceResult.noReduce
  | some f => f.impl args

end Metta
