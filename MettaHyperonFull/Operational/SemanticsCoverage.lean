-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Operational.SemanticsCoverage
Layer: Operational
Purpose: Checked examples for the four-register machine stepper. These examples cover edge cases that
  are easy to miss in proofs about the knowledge base alone, especially how a single transition consumes
  exactly one input command in the multiset-backed input register.
Imports: MettaHyperonFull.Operational.Semantics
Trusted boundary: none
Main exports: (examples only)
Open obligations: none
-/
import MettaHyperonFull.Operational.Semantics

namespace Metta

private abbrev cfg : RuntimeConfig := default
private abbrev a : Atom := Atom.sym "a"
private abbrev addDash : Atom := Atom.expr [Atom.sym "add-atom", a]
private abbrev addCamel : Atom := Atom.expr [Atom.sym "addAtom", a]
private abbrev remDash : Atom := Atom.expr [Atom.sym "remove-atom", a]
private abbrev remCamel : Atom := Atom.expr [Atom.sym "remAtom", a]

private abbrev inputState (xs : List Atom) : State := { State.empty with input := ⟨xs⟩ }
private abbrev inputKbState (xs kb : List Atom) : State := { State.empty with input := ⟨xs⟩, kb := ⟨kb⟩ }
private abbrev afterKbMutation (rest : List Atom) : State :=
  { State.empty with input := ⟨rest⟩, kb := ⟨[a]⟩, output := ⟨[Atom.unit]⟩ }

example :
    smallStep? cfg (inputState [addDash, addCamel])
      = some (StepKind.addAtom, afterKbMutation [addCamel]) :=
  rfl

example :
    smallStep? cfg (inputState [addCamel, addDash])
      = some (StepKind.addAtom, afterKbMutation [addDash]) :=
  rfl

example :
    smallStep? cfg (inputKbState [remDash, remCamel] [a, a])
      = some (StepKind.remAtom, afterKbMutation [remCamel]) :=
  rfl

example :
    smallStep? cfg (inputKbState [remCamel, remDash] [a, a])
      = some (StepKind.remAtom, afterKbMutation [remDash]) :=
  rfl

end Metta
