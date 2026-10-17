-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.Basic
Layer: Proofs
Purpose: Shared infrastructure for the metatheory layer. Supplies a structural induction principle
  for the nested inductive Atom, tagged so plain `induction a` uses it everywhere downstream, plus
  the atom reflexivity predicates and structural lemmas about variable renaming that the rest of the
  proofs reuse.
Imports: Mathlib, MettaHyperonFull
Trusted boundary: none (fully proved)
Main exports: Atom.recAux, Atom.StructurallyReflexive, Atom.MatchReflexive, renameVars_nil,
  size_renameVars
Open obligations: none
-/
import Mathlib
import MettaHyperonFull

/-!
# Metatheory infrastructure

A structural induction principle for the nested inductive `Atom`, plus structural lemmas about
variable renaming reused throughout the metatheory layer.

`induction a` does not work out of the box on `Atom`, because `Atom.expr : List Atom → Atom`
makes it a *nested* inductive. `Atom.recAux` supplies the missing principle: in the `expr`
case one may assume the motive for every immediate sub-atom. It is tagged
`@[induction_eliminator]` so plain `induction a` uses it everywhere downstream.
-/

namespace Metta

namespace Atom

/-- Structural induction for the nested inductive `Atom`: to prove `motive a` for every `a`,
handle the four constructors, and in the `expr` case assume `motive` for each immediate
sub-atom. Tagged `@[induction_eliminator]`, so `induction a` uses it. Terminates because every
sub-atom is strictly smaller in `Atom.size` (`_ha : a ∈ xs` is used in `decreasing_by`). -/
-- `nolint defLemma`: although `motive`-valued, `recAux` is an *eliminator* (tagged
-- `induction_eliminator`), so `def` rather than `theorem` is the correct form here.
@[elab_as_elim, induction_eliminator, nolint defLemma]
def recAux {motive : Atom → Prop}
    (sym : ∀ s, motive (Atom.sym s))
    (var : ∀ v, motive (Atom.var v))
    (gnd : ∀ g, motive (Atom.gnd g))
    (expr : ∀ xs, (∀ a ∈ xs, motive a) → motive (Atom.expr xs)) :
    (a : Atom) → motive a
  | Atom.sym s => sym s
  | Atom.var v => var v
  | Atom.gnd g => gnd g
  | Atom.expr xs => expr xs (fun a _ha => recAux sym var gnd expr a)
  termination_by a => a.size
  decreasing_by
    simp only [Atom.size]
    have h : Atom.size a ≤ (xs.map Atom.size).sum :=
      List.single_le_sum (by intro _ _; exact Nat.zero_le _) _ (List.mem_map_of_mem _ha)
    omega

/-- Atoms whose structural equality is reflexive. Grounded floats can include values whose host
    equality is not reflexive, so proof laws name this host-side condition explicitly. -/
def StructurallyReflexive (a : Atom) : Prop := Atom.beq a a = true

/-- Atoms that match themselves with no bindings under the executable default matcher. This is the
    exact condition needed for direct `Space.query` visibility. -/
def MatchReflexive (a : Atom) : Prop := [] ∈ matchAtoms a a

theorem sym_structurallyReflexive (s : String) : StructurallyReflexive (Atom.sym s) := by
  simp [StructurallyReflexive, Atom.beq]

theorem var_structurallyReflexive (v : VarName) : StructurallyReflexive (Atom.var v) := by
  simp [StructurallyReflexive, Atom.beq]

theorem sym_matchReflexive (s : String) : MatchReflexive (Atom.sym s) := by
  simp [MatchReflexive, matchAtoms, matchAtomsWith, Bindings.hasLoop,
    Bindings.vars]

theorem var_matchReflexive (v : VarName) : MatchReflexive (Atom.var v) := by
  simp [MatchReflexive, matchAtoms, matchAtomsWith, Bindings.hasLoop,
    Bindings.vars]

/-- Every expression headed by `Error` is an error atom, independently of the
length of its diagnostic payload. -/
@[simp]
theorem isError_errorHead (tail : List Atom) :
    (Atom.expr (Atom.sym "Error" :: tail)).isError = true := rfl

/-- The bare `Error` symbol is not itself an error result; the reserved syntax
requires an expression headed by that symbol. -/
@[simp]
theorem isError_bareError : (Atom.sym "Error").isError = false := rfl

/-- An expression with a different head remains an ordinary expression. -/
@[simp]
theorem isError_otherHead (head : String) (tail : List Atom)
    (hne : head ≠ "Error") :
    (Atom.expr (Atom.sym head :: tail)).isError = false := by
  simp [Atom.isError, hne]

/-- Error classification of a symbol-headed expression depends only on its
head, so rebuilding an application's argument tail cannot change whether it
is an error. -/
theorem isError_expr_symbol_tail_irrel
    (head : String) (left right : List Atom) :
    (Atom.expr (Atom.sym head :: left)).isError =
      (Atom.expr (Atom.sym head :: right)).isError := by
  by_cases h : head = "Error"
  · subst head
    rfl
  · simp [Atom.isError, h]

/-- `Type` is syntactically a symbol; its declared type is an environment
fact rather than a special meta-type case. -/
@[simp] theorem metaType_type : (Atom.sym "Type").metaType = .symbol := rfl

/-- The published HE semantics gives `ErrorType` no special syntactic
meaning, so it has the ordinary symbol meta-type as well. -/
@[simp] theorem metaType_errorType :
    (Atom.sym "ErrorType").metaType = .symbol := rfl

end Atom

/-- Renaming variables by the empty map is the identity. -/
theorem renameVars_nil (a : Atom) : renameVars [] a = a := by
  induction a with
  | expr xs ih => simp only [renameVars]; rw [List.map_congr_left ih]; simp
  | _ => simp [renameVars]

/-- Variable renaming preserves `Atom.size`: it replaces variables by variables, leaf-for-leaf. -/
theorem size_renameVars (m : List (VarName × VarName)) (a : Atom) :
    (renameVars m a).size = a.size := by
  induction a with
  | expr xs ih =>
      have hmap : (xs.map (renameVars m)).map Atom.size = xs.map Atom.size := by
        rw [List.map_map]; exact List.map_congr_left (fun a ha => ih a ha)
      simp only [renameVars, Atom.size, hmap]
  | _ => simp [renameVars, Atom.size]

end Metta
