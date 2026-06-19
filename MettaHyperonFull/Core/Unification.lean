import MettaHyperonFull.Core.Substitution

namespace Metta

namespace Unify

mutual

/-- Structurally decompose a single equation `a =? b` into the variable constraints it forces,
    or `none` on a head clash or arity mismatch. Trivial `$x =? $x` constraints are dropped and a
    variable on either side yields a `(var, term)` constraint. `decomposeEq` recurses mutually with
    `decomposeList` on the two atoms, so termination is structural and the function is total. -/
def decomposeEq : Atom → Atom → Option (List (VarName × Atom))
  | Atom.var x, Atom.var y => if x == y then some [] else some [(x, Atom.var y)]
  | Atom.var x, t => some [(x, t)]
  | t, Atom.var x => some [(x, t)]
  | Atom.sym a, Atom.sym b => if a == b then some [] else none
  | Atom.gnd a, Atom.gnd b => if a == b then some [] else none
  | Atom.expr xs, Atom.expr ys => decomposeList xs ys
  | _, _ => none

/-- Pointwise-decompose two argument lists (mutually with `decomposeEq`), concatenating the
    constraints; `none` on a length mismatch or any element clash. -/
def decomposeList : List Atom → List Atom → Option (List (VarName × Atom))
  | [], [] => some []
  | x :: xs, y :: ys =>
      match decomposeEq x y, decomposeList xs ys with
      | some c₁, some c₂ => some (c₁ ++ c₂)
      | _, _ => none
  | _, _ => none

end

/-- Decompose every equation in a worklist, concatenating the variable constraints, or `none` if
    any equation clashes. Structural on the worklist. -/
def decomposeAll : List (Atom × Atom) → Option (List (VarName × Atom))
  | [] => some []
  | (a, b) :: rest =>
      match decomposeEq a b, decomposeAll rest with
      | some c₁, some c₂ => some (c₁ ++ c₂)
      | _, _ => none

/-- The unification main loop, recursing structurally on `fuel`. Each round fully decomposes the
    worklist, then eliminates one variable: it substitutes `x ↦ t` into the remaining constraints
    and records the binding. Because every round removes one distinct variable from the problem,
    the number of rounds is bounded by the number of distinct variables, so `unifyTop` supplies a
    `fuel` (the total term size) that exceeds that bound; if the `fuel = 0` clause is reached with
    constraints still pending, it returns `none`. -/
def unifyRounds : Nat → List (Atom × Atom) → Subst → Option Subst
  | 0, eqs, s =>
      match decomposeAll eqs with
      | none => none
      | some [] => some s
      | some (_ :: _) => none
  | fuel + 1, eqs, s =>
      match decomposeAll eqs with
      | none => none
      | some [] => some s
      | some ((x, t) :: rest) =>
          if Subst.occurs x t then none
          else
            let sub : Subst := [(x, t)]
            let rest' := rest.map fun p => (Subst.apply sub (Atom.var p.1), Subst.apply sub p.2)
            unifyRounds fuel rest' (Subst.extend s x t)

/-- First-order syntactic unification of two atoms, returning a most-general unifier when one
    exists. Grounded atoms with custom matching are handled by `Matching.lean`, since the spec
    allows custom ground matchers. Total: decomposition is structural and elimination is bounded by
    the term size (an upper bound on the number of distinct variables). -/
def unifyTop (a b : Atom) : Option Subst :=
  unifyRounds (Atom.size a + Atom.size b) [(a, b)] []

end Unify

end Metta
