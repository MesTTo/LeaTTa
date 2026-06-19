import MettaHyperonFull.Core.Atom
import MettaHyperonFull.Core.Pretty

namespace Metta

/-- A variable-binding relation. `val x a` is `$x ← a`; `eq x y` is `$x = $y`. -/
inductive BindingRel where
  | val : VarName → Atom → BindingRel
  | eq : VarName → VarName → BindingRel
  deriving Repr, BEq, Inhabited

/-- A binding set: a conjunction of variable-binding relations, comprising value bindings `$x ← a` and
    `$x = $y` aliases (Hyperon's `Bindings`, the output of matching/unification). -/
abbrev Bindings := List BindingRel

namespace Bindings

/-- The empty binding set (no constraints). -/
def empty : Bindings := []

/-- The atom bound to `$x` by a direct `val` relation, if any (`eq` aliases are not followed). -/
def lookupVal (b : Bindings) (x : VarName) : Option Atom :=
  match b with
  | [] => none
  | BindingRel.val y a :: rest => if x == y then some a else lookupVal rest x
  | _ :: rest => lookupVal rest x

/-- The variables directly equated with `$x` by `eq` relations (one hop, both orientations). -/
def eqClasses (b : Bindings) (x : VarName) : List VarName :=
  b.foldl (fun acc r => match r with
    | BindingRel.eq a c => if a == x then c :: acc else if c == x then a :: acc else acc
    | _ => acc) []

/-- Remove direct value bindings for variable `x`; equality relations remain. -/
def removeVal (b : Bindings) (x : VarName) : Bindings :=
  b.filter (fun r => match r with | BindingRel.val y _ => y != x | _ => true)

/-- True if the set contains a trivial self-loop (`$x ← $x` or `$x = $x`), a degenerate solution
    that the matcher discards. -/
def hasLoop (b : Bindings) : Bool :=
  b.any (fun r => match r with | BindingRel.val x (Atom.var y) => x == y | BindingRel.eq x y => x == y | _ => false)

/-- Bind `$x ← a`, dropping any previous value binding for `$x`. Raw: no occurs/consistency check
    (that is `addVarBinding`'s job). -/
def addValRaw (b : Bindings) (x : VarName) (a : Atom) : Bindings := BindingRel.val x a :: removeVal b x

/-- Add the alias `$x = $y` (a no-op when `x = y`). Raw: no consistency check. -/
def addEqRaw (b : Bindings) (x y : VarName) : Bindings := if x == y then b else BindingRel.eq x y :: b

end Bindings

end Metta
