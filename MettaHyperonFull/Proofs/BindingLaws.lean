-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.BindingLaws
Layer: Proofs
Purpose: Executable binding-merge laws for `Bindings.addVarBinding`, `Bindings.addVarEquality`, and
  one-step `Bindings.merge` calls. These are the small merge facts used by matcher and simulation
  proofs: fresh variables extend, equal existing values keep the binding set, incompatible values
  fail, and unifiable values extend through the unifier boundary.
Imports: MettaHyperonFull.Proofs.Basic
Trusted boundary: none
Main exports: Bindings.lookupVal_empty, Bindings.lookupVal_addValRaw_self,
  Bindings.addVarBinding_fresh, Bindings.addVarBinding_same, Bindings.addVarBinding_conflict,
  Bindings.addVarBinding_unifies, Bindings.merge_empty_right, Bindings.merge_one_val_fresh,
  Bindings.merge_one_val_same, Bindings.merge_one_val_conflict, Bindings.merge_one_val_unifies
Open obligations: multi-binding merge associativity/permutation laws are not needed by the current
  simulation proofs and should be stated separately if a future proof requires them.
-/
import MettaHyperonFull.Proofs.Basic

namespace Metta

namespace Bindings

/-- Looking up any value in the empty binding set fails. -/
theorem lookupVal_empty (x : VarName) : lookupVal [] x = none := rfl

/-- Raw value insertion makes the inserted value immediately visible at that variable. -/
theorem lookupVal_addValRaw_self (b : Bindings) (x : VarName) (v : Atom) :
    lookupVal (addValRaw b x v) x = some v := by
  simp [addValRaw, lookupVal]

/-- A fresh value binding extends the binding set. -/
theorem addVarBinding_fresh {b : Bindings} {x : VarName} {v : Atom}
    (h : lookupVal b x = none) :
    addVarBinding b x v = [addValRaw b x v] := by
  simp [addVarBinding, h]

/-- Re-adding the same structurally reflexive value keeps the binding set unchanged. -/
theorem addVarBinding_same {b : Bindings} {x : VarName} {v : Atom}
    (hlookup : lookupVal b x = some v) (href : Atom.StructurallyReflexive v) :
    addVarBinding b x v = [b] := by
  unfold Atom.StructurallyReflexive at href
  have hbeq : (v == v) = true := href
  simp [addVarBinding, hlookup, hbeq]

/-- A conflicting value binding fails when the old and new values are neither equal nor unifiable. -/
theorem addVarBinding_conflict {b : Bindings} {x : VarName} {v previous : Atom}
    (hlookup : lookupVal b x = some previous)
    (hneq : (previous == v) = false)
    (hunify : Unify.unifyTop previous v = none) :
    addVarBinding b x v = [] := by
  simp [addVarBinding, hlookup, hneq, hunify]

/-- Distinct existing and new values may still extend the binding set when unification succeeds. -/
theorem addVarBinding_unifies {b : Bindings} {x : VarName} {v previous : Atom} {sigma : Subst}
    (hlookup : lookupVal b x = some previous)
    (hneq : (previous == v) = false)
    (hunify : Unify.unifyTop previous v = some sigma) :
    addVarBinding b x v = [addValRaw b x v] := by
  simp [addVarBinding, hlookup, hneq, hunify]

/-- Equality aliases with equal structurally reflexive values are accepted. -/
theorem addVarEquality_same {b : Bindings} {x y : VarName} {v : Atom}
    (hx : lookupVal b x = some v)
    (hy : lookupVal b y = some v)
    (href : Atom.StructurallyReflexive v) :
    addVarEquality b x y = [addEqRaw b x y] := by
  unfold Atom.StructurallyReflexive at href
  have hbeq : (v == v) = true := href
  simp [addVarEquality, hx, hy, hbeq]

/-- Equality aliases with two direct, structurally unequal values fail. -/
theorem addVarEquality_conflict {b : Bindings} {x y : VarName} {vx vy : Atom}
    (hx : lookupVal b x = some vx)
    (hy : lookupVal b y = some vy)
    (hneq : (vx == vy) = false) :
    addVarEquality b x y = [] := by
  simp [addVarEquality, hx, hy, hneq]

/-- Merging an empty right-hand binding set is the identity singleton. -/
theorem merge_empty_right (b : Bindings) : merge b [] = [b] := rfl

/-- A one-relation merge with a fresh value binding extends the binding set. -/
theorem merge_one_val_fresh {b : Bindings} {x : VarName} {v : Atom}
    (h : lookupVal b x = none) :
    merge b [BindingRel.val x v] = [addValRaw b x v] := by
  simp [merge, mergeOne, addVarBinding, h]

/-- A one-relation merge with the same structurally reflexive value keeps the binding set. -/
theorem merge_one_val_same {b : Bindings} {x : VarName} {v : Atom}
    (hlookup : lookupVal b x = some v) (href : Atom.StructurallyReflexive v) :
    merge b [BindingRel.val x v] = [b] := by
  unfold Atom.StructurallyReflexive at href
  have hbeq : (v == v) = true := href
  simp [merge, mergeOne, addVarBinding, hlookup, hbeq]

/-- A one-relation merge fails when the old and new values are neither equal nor unifiable. -/
theorem merge_one_val_conflict {b : Bindings} {x : VarName} {v previous : Atom}
    (hlookup : lookupVal b x = some previous)
    (hneq : (previous == v) = false)
    (hunify : Unify.unifyTop previous v = none) :
    merge b [BindingRel.val x v] = [] := by
  simp [merge, mergeOne, addVarBinding, hlookup, hneq, hunify]

/-- A one-relation merge extends the binding set when old and new values unify. -/
theorem merge_one_val_unifies {b : Bindings} {x : VarName} {v previous : Atom} {sigma : Subst}
    (hlookup : lookupVal b x = some previous)
    (hneq : (previous == v) = false)
    (hunify : Unify.unifyTop previous v = some sigma) :
    merge b [BindingRel.val x v] = [addValRaw b x v] := by
  simp [merge, mergeOne, addVarBinding, hlookup, hneq, hunify]

end Bindings

end Metta
