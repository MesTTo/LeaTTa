import MettaHyperonFull.Core.Substitution

namespace Metta

/-- Distinct variable names in first-occurrence order (Hyperon `atoms_are_equivalent` canonicalises
    variable names before comparing). -/
def distinctVarsAux : List VarName → List VarName → List VarName
  | [], _ => []
  | x :: xs, seen => if seen.contains x then distinctVarsAux xs seen else x :: distinctVarsAux xs (x :: seen)

/-- Rename the variables of an atom according to `m` (leaving unlisted variables unchanged). -/
def renameVars (m : List (VarName × VarName)) : Atom → Atom
  | Atom.var v => Atom.var (((m.find? (·.1 == v)).map (·.2)).getD v)
  | Atom.expr xs => Atom.expr (xs.map (renameVars m))
  | a => a

/-- Canonical form: rename each distinct variable to a positional name (`#α0`, `#α1`, …) in
    first-occurrence order, so that alpha-equivalent atoms become syntactically equal. -/
def canonicalizeVars (a : Atom) : Atom :=
  let vs := distinctVarsAux a.vars []
  renameVars (vs.zipIdx.map (fun (v, i) => (v, "#α" ++ toString i))) a

/-- Alpha-equivalence for MeTTa Core: syntactic equality up to a consistent renaming of variables
    (MeTTa variables are first-order query variables, so no binder scoping is involved). Faithful to
    Hyperon's `atoms_are_equivalent`. -/
def alphaEq (a b : Atom) : Bool := canonicalizeVars a == canonicalizeVars b

/-- Propositional α-equivalence, decided by `alphaEq`: `AlphaEquivalent a b` holds exactly when `a`
    and `b` are equal up to a consistent renaming of their variables (equality of canonical forms).
    This is the genuine α-equivalence relation, decided by the `alphaEq` Boolean. -/
def AlphaEquivalent (a b : Atom) : Prop := alphaEq a b = true

instance (a b : Atom) : Decidable (AlphaEquivalent a b) :=
  inferInstanceAs (Decidable (alphaEq a b = true))

end Metta
