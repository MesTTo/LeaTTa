/-
The category checks the elaborator runs when accepting equations and rewrites, mirroring the Scala
`AddEqRwHelpers` type checker. An equation's two sides must have compatible top-level categories; a
rewrite's two conclusion sides likewise, and every right-hand-side variable must be bound either on
the left-hand side or by a premise (`let src ~> tgt in ...` binds `tgt`).

`headCat` is the top-level category of a term: the output sort of the rule its head label names, the
body's category through a substitution, and unconstrained for a variable. Two categories are
compatible when neither is constrained (a variable matches anything) or they are equal, exactly the
Scala `sameCategory` rule.

The deeper per-variable consistency check (`catOfIdentInAST`, that every variable resolves to a single
category) is not yet implemented; these are the category-match and bound-variable checks.
-/
import MeTTaIL.Theory.Ops

namespace MeTTaIL

mutual
  /-- The variables occurring in a term (the `subst` target is bound, so excluded). -/
  def AST.vars : AST → List String
    | .var (.base n)        => [n]
    | .var (.qualified n _) => [n]
    | .sexp _ args          => AST.varsList args
    | .subst b r _          => AST.vars b ++ AST.vars r
  /-- The variables occurring in a list of terms. -/
  def AST.varsList : List AST → List String
    | []      => []
    | a :: as => AST.vars a ++ AST.varsList as
end

/-- The top-level category of a term given the function symbols: the labelled rule's output sort for
    an application, the body's category through a substitution, and unconstrained for a variable. -/
def AST.headCat (defs : List Rule) : AST → Option Cat
  | .var _       => none
  | .sexp l _    => (defs.find? (fun r => r.label == l)).map (·.cat)
  | .subst b _ _ => AST.headCat defs b

/-- Two top-level categories are compatible: an unconstrained side (a variable) matches anything, and
    two constrained sides must be equal. Mirrors `AddEqRwHelpers.sameCategory`. -/
def catCompatible : Option Cat → Option Cat → Bool
  | none,    _       => true
  | _,       none    => true
  | some c1, some c2 => c1 == c2

/-- Check an equation: its two sides have compatible top-level categories (recursing through a
    freshness guard). -/
def checkEquation (defs : List Rule) : Equation → Option String
  | .impl l r =>
      if catCompatible (l.headCat defs) (r.headCat defs) then none
      else some "equation sides have incompatible categories"
  | .fresh _ _ e => checkEquation defs e

/-- Check a rewrite: its two conclusion sides have compatible categories, and every right-hand-side
    variable is bound on the left-hand side or by a premise. -/
def checkRewrite (defs : List Rule) (rd : RewriteDecl) : Option String :=
  let lhs := rd.rw.conclusion.1
  let rhs := rd.rw.conclusion.2
  let allowed := lhs.vars ++ rd.rw.premises.map (fun h => h.tgt.baseName)
  if !catCompatible (lhs.headCat defs) (rhs.headCat defs) then
    some "rewrite sides have incompatible categories"
  else if rhs.vars.all (fun v => allowed.contains v) then none
  else some "rewrite right-hand side has a variable bound neither on the left nor by a premise"

end MeTTaIL
