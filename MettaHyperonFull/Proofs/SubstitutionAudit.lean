-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.SubstitutionAudit
Layer: Proofs
Purpose: Audit lemmas for cyclic substitutions and bindings. The core substitution is one-pass and
  has no fuel parameter. The recursive resolver used by the interpreter is deliberately bounded, and
  cyclic binding chains are not fuel-stable without an acyclicity or closed-codomain side condition.
Imports: MettaHyperonFull.Proofs.Substitution
Trusted boundary: none
Main exports: cyclicSubstXY, cyclicBindingsXY, cyclicSubst_apply_x_once,
  cyclicSubst_apply_x_twice, cyclicBindingsXY_not_direct_loop, cyclicResolve_x_one,
  cyclicResolve_x_two, cyclicResolve_not_fuel_stable
Open obligations: add a positive acyclicity theorem if a future proof needs fuel-stability rather
  than this explicit counterexample.
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

/-- `Bindings.hasLoop` rejects direct self-loops, not longer cycles. Longer cycles need a separate
    acyclicity invariant when a theorem needs fuel-stability. -/
theorem cyclicBindingsXY_not_direct_loop : Bindings.hasLoop cyclicBindingsXY = false := by
  simp [cyclicBindingsXY, Bindings.hasLoop]

theorem directValueLoop_hasLoop :
    Bindings.hasLoop [BindingRel.val "x" (Atom.var "x")] = true := by
  simp [Bindings.hasLoop]

theorem directAliasLoop_hasLoop :
    Bindings.hasLoop [BindingRel.eq "x" "x"] = true := by
  simp [Bindings.hasLoop]

theorem cyclicResolve_x_zero :
    resolveAtom cyclicBindingsXY 0 (Atom.var "x") = Atom.var "x" := by
  rfl

theorem cyclicResolve_x_one :
    resolveAtom cyclicBindingsXY 1 (Atom.var "x") = Atom.var "y" := by
  have hyx : (Atom.var "y" == Atom.var "x") = false := by
    decide
  simp [resolveAtom, cyclicBindingsXY, instantiate, bindingsToSubst, Subst.apply, Subst.lookup, hyx]

theorem cyclicResolve_x_two :
    resolveAtom cyclicBindingsXY 2 (Atom.var "x") = Atom.var "x" := by
  have hyx : (Atom.var "y" == Atom.var "x") = false := by
    decide
  have hxy : (Atom.var "x" == Atom.var "y") = false := by
    decide
  simp [resolveAtom, cyclicBindingsXY, instantiate, bindingsToSubst, Subst.apply, Subst.lookup, hyx,
    hxy]

theorem cyclicResolve_not_fuel_stable :
    resolveAtom cyclicBindingsXY 1 (Atom.var "x") ≠
      resolveAtom cyclicBindingsXY 2 (Atom.var "x") := by
  simp [cyclicResolve_x_one, cyclicResolve_x_two]

end Metta
