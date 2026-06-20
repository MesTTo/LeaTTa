/-
Module: MettaHyperonFull.Core.Substitution
Layer: Core
Purpose: Substitutions, the finite maps from variables to atoms used internally by unification and
  instantiation. Distinct from `Bindings`, which also carries variable aliases. Provides lookup, erase,
  extend, single-pass application over an atom, the occurs-check, and composition that agrees with
  function composition of the applied substitutions.
Imports: MettaHyperonFull.Core.Bindings
Trusted boundary: none
Main exports: Subst, Subst.empty, Subst.lookup, Subst.erase, Subst.extend, Subst.apply, Subst.occurs,
  Subst.compose
Open obligations: none
-/
import MettaHyperonFull.Core.Bindings

namespace Metta

/-- A substitution: a finite map from variables to atoms (distinct from `Bindings`, which also
    carries `eq` aliases). The form used internally by unification and `instantiate`. -/
abbrev Subst := List (VarName × Atom)

namespace Subst

def empty : Subst := []

def lookup (s : Subst) (x : VarName) : Option Atom :=
  match s with
  | [] => none
  | (y,a) :: rest => if x == y then some a else lookup rest x

def erase (s : Subst) (x : VarName) : Subst := s.filter (fun p => p.fst != x)

/-- Extend `s` with `$x ↦ a`, replacing any previous assignment for `$x`. -/
def extend (s : Subst) (x : VarName) (a : Atom) : Subst := (x,a) :: erase s x

/-- Apply `s` to an atom: replace each variable by its assigned value (one pass; the substituted
    value is not itself re-substituted). Structural on the atom, hence total. -/
def apply (s : Subst) : Atom → Atom
  | Atom.var x => (lookup s x).getD (Atom.var x)
  | Atom.expr xs => Atom.expr (xs.map (apply s))
  | a => a

/-- Occurs-check: does variable `$x` appear anywhere in the atom? Used by unification to reject the
    cyclic binding `$x ↦ … $x …`. -/
def occurs (x : VarName) : Atom → Bool
  | Atom.var y => x == y
  | Atom.expr xs => xs.attach.any (fun ⟨a, _⟩ => occurs x a)
  | _ => false

/-- Composition: apply `s1` to each of `s2`'s targets, then prepend `s1`, so that
    `apply (compose s1 s2)` agrees with `apply s1 ∘ apply s2`. -/
def compose (s1 s2 : Subst) : Subst :=
  s2.map (fun p => (p.fst, apply s1 p.snd)) ++ s1

end Subst

end Metta
