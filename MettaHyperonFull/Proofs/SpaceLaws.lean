-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.SpaceLaws
Layer: Proofs
Purpose: Basic atomspace mutation laws for the list-backed `Space`: inserting a structurally or
  matcher-reflexive atom makes it visible, removing immediately after a fresh insert restores the
  previous multiset, and inserted type/equality declarations are visible to the corresponding
  readers.
Imports: MettaHyperonFull.Proofs.Basic
Trusted boundary: none
Main exports: Atom.StructurallyReflexive, Atom.MatchReflexive, Space.insert_contains_self,
  Space.query_insert_self, Space.removeOne_insert_self, Space.typeAssignments_insert_visible,
  Space.equalityRules_insert_visible
Open obligations: named-space and state-cell visibility are proved at the interpreter/world layer.
-/
import MettaHyperonFull.Proofs.Basic

namespace Metta

namespace Atom

/-- Atoms whose structural equality is reflexive. Grounded floats can include values whose host
    equality is not reflexive, so space visibility laws name this host-side condition explicitly. -/
def StructurallyReflexive (a : Atom) : Prop := Atom.beq a a = true

/-- Atoms that match themselves with no bindings under the executable space-query matcher. This is
    the exact condition needed for direct `Space.query` visibility. -/
def MatchReflexive (a : Atom) : Prop := [] ∈ matchAtoms a a

theorem sym_structurallyReflexive (s : String) : StructurallyReflexive (Atom.sym s) := by
  simp [StructurallyReflexive, Atom.beq]

theorem var_structurallyReflexive (v : VarName) : StructurallyReflexive (Atom.var v) := by
  simp [StructurallyReflexive, Atom.beq]

theorem sym_matchReflexive (s : String) : MatchReflexive (Atom.sym s) := by
  simp [MatchReflexive, matchAtoms, matchAtomsWith]

theorem var_matchReflexive (v : VarName) : MatchReflexive (Atom.var v) := by
  simp [MatchReflexive, matchAtoms, matchAtomsWith]

end Atom

namespace Space

/-- Adding a structurally reflexive atom makes it visible to `contains`. -/
theorem insert_contains_self (s : Space) (a : Atom) (h : Atom.StructurallyReflexive a) :
    (s.insert a).contains a = true := by
  have hbeq : (a == a) = true := h
  simp [Space.insert, Space.contains]
  exact Or.inl hbeq

/-- Adding a matcher-reflexive atom makes it visible to `query` with the empty binding. -/
theorem query_insert_self (s : Space) (a : Atom) (h : Atom.MatchReflexive a) :
    [] ∈ (s.insert a).query a := by
  unfold Atom.MatchReflexive at h
  simp [Space.insert, Space.query]
  exact Or.inl h

/-- Removing exactly the structurally reflexive atom just inserted restores the previous multiset. -/
theorem removeOne_insert_self (s : Space) (a : Atom) (h : Atom.StructurallyReflexive a) :
    (s.insert a).removeOne a = s := by
  have hbeq : (a == a) = true := h
  cases s
  simp [Space.insert, Space.removeOne, Space.removeOne.removeFirst, hbeq]

/-- A freshly inserted `(: a ty)` declaration is visible when the subject is structurally reflexive. -/
theorem typeAssignments_insert_visible (s : Space) (a ty : Atom)
    (h : Atom.StructurallyReflexive a) :
    ty ∈ (s.insert (Atom.expr [Atom.sym ":", a, ty])).typeAssignments a := by
  have hbeq : (a == a) = true := h
  simp [Space.insert, Space.typeAssignments]
  exact Or.inl hbeq

/-- A freshly inserted `(= lhs rhs)` rule is visible to `equalityRules`. -/
theorem equalityRules_insert_visible (s : Space) (lhs rhs : Atom) :
    (lhs, rhs) ∈ (s.insert (Atom.expr [Atom.sym "=", lhs, rhs])).equalityRules := by
  simp [Space.insert, Space.equalityRules]

end Space

end Metta
