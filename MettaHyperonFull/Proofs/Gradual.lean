-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.Gradual
Layer: Proofs
Purpose: Gradual type consistency as a relation. MeTTa's type compatibility (Hyperon's match_types)
  is Siek and Taha's consistency relation: reflexive and symmetric but pointedly not transitive,
  because Number is consistent with %Undefined% and %Undefined% with String, yet Number is not
  consistent with String. The intransitivity is what keeps the dynamic type sound instead of
  collapsing every type into one, so compatibility is a tolerance relation, not a preorder. The
  kernel's running matchType is shown to inherit the same non-transitivity.
Imports: MettaHyperonFull.Proofs.TypeSoundness
Trusted boundary: none (fully proved)
Main exports: Consistent, ConsistentList, Consistent.refl, Consistent.symm,
  Consistent.not_consistent_distinct_syms, Consistent.number_not_consistent_string,
  Consistent.not_transitive, matchType_number_string_none, matchType_not_transitive
Open obligations: none
-/
import MettaHyperonFull.Proofs.TypeSoundness

/-!
# Metatheory: gradual type consistency

MeTTa is *gradually* typed: the dynamic type `%Undefined%` (and the top meta-type `Atom`) is
compatible with every type, and type-checking accepts an argument whose type is *consistent* with
the parameter's, not necessarily equal. Operationally, Hyperon's `match_types` implements exactly
this: `%Undefined%`/`Atom` are wildcards on either side; otherwise the two types are unified
structurally (`Proofs/TypeSoundness.lean : matchType_undefined_left/right`, `matchType_atom_left`).

This file gives that compatibility its declarative form as the **consistency relation** `~` of Siek &
Taha's gradual typing, and proves its characteristic algebra:

* `Consistent.refl` / `Consistent.symm`: `~` is **reflexive and symmetric**;
* `Consistent.not_transitive`: `~` is **not transitive**.
  Concretely: `Number ~ %Undefined%` and `%Undefined% ~ String`, yet `Number ≁ String`. Were `~`
  transitive, routing through `%Undefined%` would relate all types and make the type system vacuous.
  Gradual typing keeps the dynamic type compatible-with-everything by giving up transitivity.

MeTTa's type compatibility is a *tolerance* relation (reflexive + symmetric, intransitive), not a
preorder. That is what makes the `%Undefined%`/`Atom` escape hatch sound without collapsing the
whole type discipline.
-/

namespace Metta

mutual
/-- Gradual type **consistency** `t₁ ~ t₂` (Siek-Taha): equal types are consistent; the dynamic type
`%Undefined%` and the top meta-type `Atom` are consistent with anything on either side; and two
expressions are consistent when they have equal length and pointwise-consistent components (so
`(-> A B) ~ (-> A %Undefined%)`). Mirrors Hyperon's `match_types`. -/
inductive Consistent : Atom → Atom → Prop where
  | same   (t : Atom)               : Consistent t t
  | undefL (t : Atom)               : Consistent (Atom.sym "%Undefined%") t
  | undefR (t : Atom)               : Consistent t (Atom.sym "%Undefined%")
  | atomL  (t : Atom)               : Consistent (Atom.sym "Atom") t
  | atomR  (t : Atom)               : Consistent t (Atom.sym "Atom")
  | expr   {xs ys : List Atom}      : ConsistentList xs ys → Consistent (Atom.expr xs) (Atom.expr ys)
/-- Pointwise consistency of two type-argument lists (companion of `Consistent` for expressions). -/
inductive ConsistentList : List Atom → List Atom → Prop where
  | nil  : ConsistentList [] []
  | cons {a b : Atom} {xs ys : List Atom} :
      Consistent a b → ConsistentList xs ys → ConsistentList (a :: xs) (b :: ys)
end

namespace Consistent

/-- `~` is **reflexive**. -/
protected theorem refl (t : Atom) : Consistent t t := .same t

mutual
/-- `~` is **symmetric**. (The constructor arguments of `same`/`undef*`/`atom*` are pinned by index
unification, so the goal already determines them, hence `exact .same _` etc.) -/
theorem symm {a b : Atom} (h : Consistent a b) : Consistent b a := by
  cases h with
  | same _   => exact .same _
  | undefL _ => exact .undefR _
  | undefR _ => exact .undefL _
  | atomL _  => exact .atomR _
  | atomR _  => exact .atomL _
  | expr hl  => exact .expr (symmList hl)
/-- Symmetry, lifted pointwise to argument lists. -/
theorem symmList {xs ys : List Atom} (h : ConsistentList xs ys) : ConsistentList ys xs := by
  cases h with
  | nil          => exact .nil
  | cons hab hxs => exact .cons (symm hab) (symmList hxs)
end

/-- Two **distinct** symbols, *neither* of which is a gradual wildcard (`%Undefined%`/`Atom`), are
never consistent: no constructor of `~` applies (the `expr` case is a symbol/expression clash). The
non-transitivity counterexample is a corollary of this. -/
theorem not_consistent_distinct_syms {a b : String}
    (hab : a ≠ b) (hua : a ≠ "%Undefined%") (htA : a ≠ "Atom")
    (hub : b ≠ "%Undefined%") (htB : b ≠ "Atom") :
    ¬ Consistent (Atom.sym a) (Atom.sym b) := by
  intro h
  cases h with
  | same   => exact hab rfl
  | undefL => exact hua rfl
  | undefR => exact hub rfl
  | atomL  => exact htA rfl
  | atomR  => exact htB rfl

/-- A concrete incompatibility: `Number ≁ String` (neither is `%Undefined%`/`Atom`, they are unequal
symbols, and they are not expressions). The witness used for non-transitivity below. -/
theorem number_not_consistent_string : ¬ Consistent (Atom.sym "Number") (Atom.sym "String") :=
  not_consistent_distinct_syms (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Gradual typing's defining property: consistency is NOT transitive.** `Number ~ %Undefined%`
(everything is consistent with the dynamic type) and `%Undefined% ~ String`, but `Number ≁ String`.
A transitive `~` would, via `%Undefined%`, relate every pair of types and make the type system
vacuous; gradual typing deliberately sacrifices transitivity to keep `%Undefined%` sound. -/
theorem not_transitive :
    ¬ (∀ a b c : Atom, Consistent a b → Consistent b c → Consistent a c) := by
  intro htrans
  exact number_not_consistent_string
    (htrans (Atom.sym "Number") (Atom.sym "%Undefined%") (Atom.sym "String")
      (.undefR _) (.undefL _))

end Consistent

/-! ## The executable `matchType` inherits gradual consistency

`Consistent` above is the *declarative* relation. We also show the kernel's actual type matcher
(`Minimal/Interpreter.lean : matchType`, matching Hyperon's `match_types`) exhibits the same
defining algebra: it is **not transitive**, the operational counterpart of
`Consistent.not_transitive`. Non-transitivity is a property of the code that runs, not only of
a declarative relation beside it. -/

open Metta.Minimal

/-- `Number` and `String` are rejected by the kernel's `matchType` (neither is a gradual wildcard, and
they are unequal symbols): the operational witness `matchType … Number String = none`. -/
theorem matchType_number_string_none (tb : Bindings) :
    matchType tb (Atom.sym "Number") (Atom.sym "String") = none := by
  have h1 : (Atom.sym "Number" == Atom.sym "%Undefined%") = false := by decide
  have h2 : (Atom.sym "String" == Atom.sym "%Undefined%") = false := by decide
  have h3 : (Atom.sym "Number" == Atom.sym "Atom") = false := by decide
  have h4 : (Atom.sym "String" == Atom.sym "Atom") = false := by decide
  have h5 : ("Number" == "String") = false := by decide
  simp [matchType, matchReduced, matchAtoms, matchAtomsWith, h1, h2, h3, h4, h5]

/-- **The kernel's `matchType` is not transitive**: the running-code counterpart of
`Consistent.not_transitive`. `matchType` accepts `Number` against `%Undefined%`
(`matchType_undefined_right`) and `%Undefined%` against `String` (`matchType_undefined_left`), yet
rejects `Number` against `String`. The gradual dynamic type is a compatibility *tolerance*, not a
transitive relation, and that holds for the function the interpreter actually evaluates. -/
theorem matchType_not_transitive :
    ¬ ∀ (a b c : Atom), matchType [] a b = some [] → matchType [] b c = some [] →
        matchType [] a c = some [] := by
  intro htrans
  have key := htrans (Atom.sym "Number") (Atom.sym "%Undefined%") (Atom.sym "String")
    (matchType_undefined_right [] (Atom.sym "Number"))
    (matchType_undefined_left [] (Atom.sym "String"))
  rw [matchType_number_string_none] at key
  simp at key

end Metta
