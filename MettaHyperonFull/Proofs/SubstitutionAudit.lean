-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.SubstitutionAudit
Layer: Proofs
Purpose: Audit lemmas for cyclic substitutions and bindings. Raw substitution remains one-pass,
  while equality-class-aware binding resolution detects longer dependency cycles, leaves cyclic
  instantiation unchanged, and makes the interpreter's bounded resolver fuel-stable on rejection.
Imports: MettaHyperonFull.Proofs.Substitution
Trusted boundary: none
Main exports: cyclicSubstXY, cyclicBindingsXY, cyclicSubst_apply_x_once,
  cyclicSubst_apply_x_twice, cyclicBindingsXY_hasLoop, cyclicBindingsXY_instantiate_x,
  cyclicResolve_x_stable
Open obligations: none
-/
import MettaHyperonFull.Proofs.Substitution

namespace Metta
open Metta.Minimal

/-- A two-variable cycle as a raw substitution. -/
def cyclicSubstXY : Subst := [("x", Atom.var "y"), ("y", Atom.var "x")]

/-- The same two-variable cycle as matcher bindings. -/
def cyclicBindingsXY : Bindings :=
  [BindingRel.val "x" (Atom.var "y"), BindingRel.val "y" (Atom.var "x")]

theorem cyclicSubst_apply_x_once :
    Subst.apply cyclicSubstXY (Atom.var "x") = Atom.var "y" := by
  simp [cyclicSubstXY, Subst.apply, Subst.lookup]

theorem cyclicSubst_apply_y_once :
    Subst.apply cyclicSubstXY (Atom.var "y") = Atom.var "x" := by
  simp [cyclicSubstXY, Subst.apply, Subst.lookup]

/-- Reapplying the same cyclic substitution can change the result again. This is why there is no
    unconditional fuel-stability theorem for repeated substitution expansion. -/
theorem cyclicSubst_apply_x_twice :
    Subst.apply cyclicSubstXY (Subst.apply cyclicSubstXY (Atom.var "x")) = Atom.var "x" := by
  simp [cyclicSubstXY, Subst.apply, Subst.lookup]

/-- Equality-class-aware loop detection rejects a two-variable dependency cycle. -/
theorem cyclicBindingsXY_hasLoop : Bindings.hasLoop cyclicBindingsXY = true := by
  have hxy : ("x" == "y") = false := by decide
  have hyx : ("y" == "x") = false := by decide
  change Bindings.hasLoop
    [BindingRel.val "x" (Atom.var "y"),
      BindingRel.val "y" (Atom.var "x")] = true
  have hclass := Bindings.classValues_eq_lookupVal_toList_of_eqVarsInOrder_nil
    (b := [BindingRel.val "x" (Atom.var "y"),
      BindingRel.val "y" (Atom.var "x")]) (by rfl)
  simp (config := { maxSteps := 1000000 }) [Bindings.hasLoop,
    Bindings.vars, Bindings.resolveAtomAux, Bindings.resolutionFuel,
    Bindings.relationResolutionFuel, hclass, Bindings.lookupVal,
    Bindings.eqRepresentative, Bindings.eqClassOrdered, Bindings.eqClass,
    Bindings.eqClassAux, Bindings.eqStep, Bindings.eqVarsInOrder, Atom.size, Atom.vars,
    hxy, hyx]

theorem directValueLoop_hasLoop :
    Bindings.hasLoop [BindingRel.val "x" (Atom.var "x")] = true := by
  simp [Bindings.hasLoop]

theorem directAliasLoop_hasLoop :
    Bindings.hasLoop [BindingRel.eq "x" "x"] = true := by
  simp [Bindings.hasLoop]

/-- A rejected cyclic binding does not partially instantiate its input. -/
theorem cyclicBindingsXY_instantiate_x :
    instantiate cyclicBindingsXY (Atom.var "x") = Atom.var "x" := by
  change instantiate
    [BindingRel.val "x" (Atom.var "y"),
      BindingRel.val "y" (Atom.var "x")]
    (Atom.var "x") = Atom.var "x"
  have hclass := Bindings.classValues_eq_lookupVal_toList_of_eqVarsInOrder_nil
    (b := [BindingRel.val "x" (Atom.var "y"),
      BindingRel.val "y" (Atom.var "x")]) (by rfl)
  simp (config := { maxSteps := 1000000 }) [instantiate,
    Bindings.resolveAtom, Bindings.resolve, Bindings.resolveAtomAux, Bindings.resolutionFuel,
    Bindings.relationResolutionFuel, hclass, Bindings.lookupVal,
    Bindings.eqClassOrdered,
    Bindings.eqClass, Bindings.eqClassAux, Bindings.eqStep, Bindings.eqVarsInOrder,
    Atom.size]

/-- Once a cycle is rejected, every fuel bound gives the same unchanged result. -/
theorem cyclicResolve_x_stable (fuel : Nat) :
    resolveAtom cyclicBindingsXY fuel (Atom.var "x") = Atom.var "x" := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [resolveAtom, cyclicBindingsXY_instantiate_x]
      rw [if_pos (by decide)]

end Metta
