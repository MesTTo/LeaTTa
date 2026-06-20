/-
Module: MettaHyperonFull.Proofs.Alpha
Layer: Proofs
Purpose: α-equivalence of atoms, defined as equality of canonical forms. Proves it is an equivalence
  relation, that it preserves atom size, and that it collapses to syntactic equality on variable-free
  atoms. Documents why the kernel's Boolean decider is faithful only on the float-free fragment,
  because host IEEE floats make BEq Atom unlawful.
Imports: MettaHyperonFull.Proofs.Basic
Trusted boundary: none (fully proved)
Main exports: AlphaEq, alphaEq_equivalence, alphaSetoid, AlphaEq.size_eq, alphaEq_iff_eq_of_closed
Open obligations: none
-/
import MettaHyperonFull.Proofs.Basic

/-!
# Metatheory: α-equivalence

MeTTa's variables are first-order *query* variables with **atom-global scope**; there are no
binders, hence none of the local scoping of the λ-calculus. Two atoms are α-equivalent when one
is obtained from the other by a consistent renaming of variables. The kernel decides this by
canonicalising variable names in first-occurrence order (`canonicalizeVars`) and comparing
(`alphaEq`, in `Core/Alpha.lean`), matching Hyperon's `atoms_are_equivalent`.

Three facts are proved here:

* `alphaEq_equivalence`:      α-equivalence (equal canonical forms) is an **equivalence relation**;
* `AlphaEq.size_eq`:          α-equivalent atoms have the **same size** (renaming cannot change shape);
* `alphaEq_iff_eq_of_closed`: on **variable-free** atoms, α-equivalence collapses to syntactic `=`.

## The Boolean decider and host floats

We state α-equivalence *propositionally* as
`AlphaEq a b := canonicalizeVars a = canonicalizeVars b`, rather than through the kernel's
Boolean `alphaEq`. `Atom` contains `Ground.float : Float → Ground`, and
Lean's `Float` equality is IEEE 754: `nan == nan` is `false`, and `0.0 == (-0.0)` is `true` while
`0.0 ≠ -0.0`. The derived `BEq Atom` is therefore **not lawful** (`LawfulBEq Atom` is false), so
the Boolean `alphaEq` is not reflexive on atoms containing `NaN`. `#eval` confirms
`alphaEq (gnd (float (0.0/0.0))) (gnd (float (0.0/0.0))) = false`, and it conflates `±0.0`. The
Boolean is the correct decision procedure for `AlphaEq` on the float-free fragment; the
propositional relation is an equivalence relation unconditionally. Hyperon inherits the same
host-float behavior, so the propositional form is faithful to the implementation.
-/

namespace Metta

/-- Propositional α-equivalence: two atoms are α-equivalent when they share a canonical form, i.e.
are equal up to a consistent renaming of their (atom-global, unscoped) query variables. The
kernel's Boolean `alphaEq` decides this relation on the float-free fragment; see the module
docstring for the host-float caveat. -/
def AlphaEq (a b : Atom) : Prop := canonicalizeVars a = canonicalizeVars b

/-- **α-equivalence is an equivalence relation** (reflexive, symmetric, transitive). -/
theorem alphaEq_equivalence : Equivalence AlphaEq :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- α-equivalence packaged as a `Setoid`, so the quotient `Atom / AlphaEq` is available to
downstream developments. -/
def alphaSetoid : Setoid Atom := ⟨AlphaEq, alphaEq_equivalence⟩

/-- Canonicalisation preserves `Atom.size`. -/
theorem size_canonicalizeVars (a : Atom) : (canonicalizeVars a).size = a.size := by
  simp only [canonicalizeVars]; exact size_renameVars _ a

/-- α-equivalent atoms have the same size: a consistent renaming cannot change an atom's shape. -/
theorem AlphaEq.size_eq {a b : Atom} (h : AlphaEq a b) : a.size = b.size := by
  have ha := size_canonicalizeVars a
  have hb := size_canonicalizeVars b
  rw [← ha, ← hb, h]

/-- A variable-free atom is its own canonical form. -/
theorem canonicalizeVars_of_closed {a : Atom} (h : a.vars = []) : canonicalizeVars a = a := by
  simp only [canonicalizeVars, h, distinctVarsAux, List.zipIdx_nil, List.map_nil]
  exact renameVars_nil a

/-- On variable-free atoms, α-equivalence coincides with syntactic equality. -/
theorem alphaEq_iff_eq_of_closed {a b : Atom} (ha : a.vars = []) (hb : b.vars = []) :
    AlphaEq a b ↔ a = b := by
  unfold AlphaEq
  rw [canonicalizeVars_of_closed ha, canonicalizeVars_of_closed hb]

end Metta
