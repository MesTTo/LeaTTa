-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Theory.Check
Layer: Theory
Purpose: The category checks the elaborator runs when accepting equations and rewrites, mirroring the
  Scala `AddEqRwHelpers` type checker. An equation's two sides must have compatible top-level
  categories, a rewrite's two conclusion sides likewise, and every right-hand-side variable must be
  bound on the left-hand side or by a premise (`let src ~> tgt in ...` binds both `src` and `tgt`, as
  Scala's `leftVars` does). `catCompatible` treats an undetermined side as compatible with anything, so
  it is more permissive than Scala's `sameCategory` in three edge cases the tested modules never hit.
  Variables compare by base identifier (`DottedPath.baseName`), matching the matcher in
  `Semantics/Reduce`, where Scala uses the full dotted-path string.
Imports: MeTTaIL.Theory.Ops
Trusted boundary: none
Main exports: AST.vars, AST.headCat, catCompatible, checkEquation, checkRewrite
Open obligations: the deeper per-variable consistency check (`catOfIdentInAST`, that every variable
  resolves to a single category) is not yet implemented; these are the category-match and
  bound-variable checks.
-/
import MeTTaIL.Theory.Ops

namespace MeTTaIL

mutual
  /-- The variables occurring in a term, including the substitution target. Mirrors Scala
      `ASTHelpers.varsInAST`, which adds the target dotted-path to the variables of the body and the
      replacement. -/
  def AST.vars : AST → List String
    | .var (.base n)        => [n]
    | .var (.qualified n _) => [n]
    | .sexp _ args          => AST.varsList args
    | .subst b r t          => AST.vars b ++ AST.vars r ++ [t.baseName]
  /-- The variables occurring in a list of terms. -/
  def AST.varsList : List AST → List String
    | []      => []
    | a :: as => AST.vars a ++ AST.varsList as
end

/-- The top-level category of a term given the function symbols: the labelled rule's output sort for
    an application, the body's category through a substitution, and `none` (undetermined) for a
    variable or a head label that names no rule. -/
def AST.headCat (defs : List Rule) : AST → Option Cat
  | .var _       => none
  | .sexp l _    => (defs.find? (fun r => r.label == l)).map (·.cat)
  | .subst b _ _ => AST.headCat defs b

/-- Two top-level categories are compatible: an undetermined side (`none`) matches anything, and two
    determined sides must be equal. A more permissive version of `AddEqRwHelpers.sameCategory` (see the
    note at the top of the file on the two cases Scala additionally rejects). -/
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
  let allowed := lhs.vars ++ rd.rw.premises.flatMap (fun h => [h.src.baseName, h.tgt.baseName])
  if !catCompatible (lhs.headCat defs) (rhs.headCat defs) then
    some "rewrite sides have incompatible categories"
  else if rhs.vars.all (fun v => allowed.contains v) then none
  else some "rewrite right-hand side has a variable bound neither on the left nor by a premise"

end MeTTaIL
