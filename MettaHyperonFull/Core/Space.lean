/-
Module: MettaHyperonFull.Core.Space
Layer: Core
Purpose: The MeTTa space (Atomspace), modelled as a multiset of atoms backed by a list. Duplicates are
  kept, so adding the same atom twice makes it match twice, as in Hyperon. Provides the space
  operations (insert, append, contains, single-copy removal), the query primitive over patterns, the
  match-and-instantiate transform, and the readers for type assignments and equality rules.
Imports: MettaHyperonFull.Core.Matching
Trusted boundary: none
Main exports: Space, Space.empty, Space.singleton, Space.insert, Space.append, Space.contains,
  Space.removeOne, Space.query, Space.transform, Space.typeAssignments, Space.equalityRules
Open obligations: none
-/
import MettaHyperonFull.Core.Matching

namespace Metta

/-- A MeTTa space/Atomspace, as an executable list of atoms (a bag, not a set). -/
structure Space where
  /-- The atoms held by the space. Duplicates are kept: adding the same atom twice makes it
      match twice, as in Hyperon, which is why `removeOne` removes a single copy. The list is
      stored in insertion order, but that order is not semantically significant. -/
  atoms : List Atom
  deriving BEq, Inhabited, Repr

namespace Space

def empty : Space := ⟨[]⟩
def singleton (a : Atom) : Space := ⟨[a]⟩
/-- Add `a` to the space (prepended; multiset semantics, so duplicates are kept). -/
def insert (s : Space) (a : Atom) : Space := ⟨a :: s.atoms⟩
def append (s t : Space) : Space := ⟨s.atoms ++ t.atoms⟩
def contains (s : Space) (a : Atom) : Bool := s.atoms.any (fun x => x == a)
/-- Remove the first occurrence of `a` from the space (multiset removal: one copy). -/
def removeOne (s : Space) (a : Atom) : Space := ⟨removeFirst s.atoms a⟩
where
  removeFirst : List Atom → Atom → List Atom
    | [], _ => []
    | x :: xs, a => if x == a then xs else x :: removeFirst xs a

/-- All binding sets under which `pattern` matches some atom of the space (the space-query primitive). -/
def query (s : Space) (pattern : Atom) : List Bindings :=
  s.atoms.flatMap (fun a => matchAtoms pattern a)

/-- Query with `pattern`, then instantiate `tmpl` under each resulting binding (MeTTa `match`). -/
def transform (s : Space) (pattern tmpl : Atom) : List Atom :=
  (query s pattern).map (fun b => instantiate b tmpl)

/-- The declared types of `a`: the `ty` of every `(: a ty)` atom in the space. -/
def typeAssignments (s : Space) (a : Atom) : List Atom :=
  s.atoms.filterMap (fun x => match x with
    | Atom.expr [Atom.sym ":", lhs, ty] => if lhs == a then some ty else none
    | _ => none)

/-- The `(= lhs rhs)` equality rules of the space, as `(lhs, rhs)` pairs. -/
def equalityRules (s : Space) : List (Atom × Atom) :=
  s.atoms.filterMap (fun x => match x with
    | Atom.expr [Atom.sym "=", lhs, rhs] => some (lhs,rhs)
    | _ => none)

end Space

end Metta
