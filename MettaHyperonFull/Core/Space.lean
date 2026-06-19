import MettaHyperonFull.Core.Matching

namespace Metta

/-- A MeTTa space/Atomspace. We use a list as an executable multiset representation. -/
structure Space where
  /-- The atoms held by the space, as a list (multiset: order and duplicates are not significant). -/
  atoms : List Atom
  deriving BEq, Inhabited, Repr

namespace Space

/-- The empty space. -/
def empty : Space := ⟨[]⟩
/-- The space containing exactly the atom `a`. -/
def singleton (a : Atom) : Space := ⟨[a]⟩
/-- Add `a` to the space (prepended; multiset semantics, so duplicates are kept). -/
def insert (s : Space) (a : Atom) : Space := ⟨a :: s.atoms⟩
/-- The multiset union of two spaces (their atom lists concatenated). -/
def append (s t : Space) : Space := ⟨s.atoms ++ t.atoms⟩
/-- Whether the space contains an atom equal to `a`. -/
def contains (s : Space) (a : Atom) : Bool := s.atoms.any (fun x => x == a)
/-- Remove the first occurrence of `a` from the space (multiset removal: one copy). -/
def removeOne (s : Space) (a : Atom) : Space := ⟨removeFirst s.atoms a⟩
where
  /-- Drop the first list element equal to `a`, leaving the rest unchanged. -/
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
