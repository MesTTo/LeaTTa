/-
Module: MettaHyperonFull.Core.FreeVars
Layer: Core
Purpose: The free variables of an atom, kept as a named notion for the metatheory. Atoms have no
  binders, so the free variables are exactly the variable occurrences (`Atom.vars`). Also gives the
  closedness (ground) predicate and a small proof about it.
Imports: MettaHyperonFull.Core.Atom
Trusted boundary: none
Main exports: freeVars, isGround, isGround_sym
Open obligations: none
-/
import MettaHyperonFull.Core.Atom

namespace Metta

/-- The free variables of `a`. Atoms have no binders, so this is exactly its variable occurrences
    (`Atom.vars`); kept as a named notion because the metatheory reasons about free variables. -/
def freeVars (a : Atom) : List VarName := Atom.vars a

/-- True if `a` is closed (contains no variables), i.e. a *ground* atom. -/
def isGround (a : Atom) : Bool := freeVars a == []

theorem isGround_sym (s : String) : isGround (Atom.sym s) = true := by
  simp [isGround, freeVars, Atom.vars]

end Metta
