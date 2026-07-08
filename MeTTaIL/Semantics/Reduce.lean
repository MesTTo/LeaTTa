-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Semantics.Reduce
Layer: Semantics
Purpose: The GSLT reduction core, where a presentation's rewrites drive computation on terms. A rewrite
  `lhs ~> rhs` applies to a term `t` when `lhs` matches `t` (first-order matching binds the pattern
  variables to subterms); the contractum is `rhs` instantiated with those bindings, with the built-in
  `Subst` resolved. These are the base-rewrite steps (no premises). Premised rewrites (the congruence
  rules) build on this in `Semantics/Relation.lean`. The equations are stored on the presentation but
  are not yet reflected in any reduction relation. Matching and the traversals are hand-written by
  mutual recursion because `AST` nests through `List`.
Imports: MeTTaIL.Theory.Ops
Trusted boundary: human-reviewed spec
Main exports: AST.matchPat, AST.subst1, AST.inst, applyBaseRewrite, baseReducts
Open obligations: the equations are stored on the presentation but are not yet reflected in any
  reduction relation.
-/
import MeTTaIL.Theory.Ops

namespace MeTTaIL

mutual
  /-- First-order matching of a pattern against a term, threading the variable bindings. A pattern
      variable matches any subterm (and must match consistently if it recurs); constructors match
      structurally; everything else matches only itself. -/
  def AST.matchPat : AST → AST → List (String × AST) → Option (List (String × AST))
    | .var (.base v), t, bnds =>
        match bnds.find? (fun b => b.1 == v) with
        | some (_, t') => if t' == t then some bnds else none
        | none => some ((v, t) :: bnds)
    | .sexp l ps, .sexp m ts, bnds => if l == m then AST.matchPatList ps ts bnds else none
    | .subst pb pr pv, .subst tb tr tv, bnds =>
        if pv == tv then (AST.matchPat pb tb bnds).bind (AST.matchPat pr tr) else none
    | p, t, bnds => if p == t then some bnds else none
  /-- Match a list of patterns against a list of terms, pointwise. -/
  def AST.matchPatList :
      List AST → List AST → List (String × AST) → Option (List (String × AST))
    | [], [], bnds => some bnds
    | p :: ps, t :: ts, bnds => (AST.matchPat p t bnds).bind (AST.matchPatList ps ts)
    | _, _, _ => none
end

mutual
  /-- Substitute `repl` for the variable `v` in a term. The `Subst` node's own variable is not a
      binder in the term tree (binders live in the grammar, not the AST), so this is plain
      replacement. -/
  def AST.subst1 (v : DottedPath) (repl : AST) : AST → AST
    | .var p => if p == v then repl else .var p
    | .sexp l args => .sexp l (AST.subst1List v repl args)
    | .subst b r w => .subst (AST.subst1 v repl b) (AST.subst1 v repl r) w
  /-- Substitute through a list of terms. -/
  def AST.subst1List (v : DottedPath) (repl : AST) : List AST → List AST
    | [] => []
    | a :: as => AST.subst1 v repl a :: AST.subst1List v repl as
end

mutual
  /-- Instantiate a term with variable bindings, resolving any `Subst` node. For `Subst body repl w`,
      if the pattern variable `w` is bound to a term variable, substitution targets that variable's
      path (the bound name); otherwise it targets `w` directly. -/
  def AST.inst (bnds : List (String × AST)) : AST → AST
    | .var (.base v) =>
        match bnds.find? (fun b => b.1 == v) with
        | some (_, t) => t
        | none => .var (.base v)
    | .var p => .var p
    | .sexp l args => .sexp l (AST.instList bnds args)
    | .subst b r w =>
        let w' :=
          match w with
          | .base name =>
              match bnds.find? (fun b => b.1 == name) with
              | some (_, .var p) => p
              | _ => w
          | _ => w
        AST.subst1 w' (AST.inst bnds r) (AST.inst bnds b)
  /-- Instantiate a list of terms. -/
  def AST.instList (bnds : List (String × AST)) : List AST → List AST
    | [] => []
    | a :: as => AST.inst bnds a :: AST.instList bnds as
end

/-- Apply a base rewrite (one with no premises) to a term: match its left-hand side, then instantiate
    its right-hand side. Returns `none` if the rewrite has premises or does not match. -/
def applyBaseRewrite (rd : RewriteDecl) (t : AST) : Option AST :=
  match rd.rw with
  | .base lhs rhs => (AST.matchPat lhs t []).map (fun bnds => AST.inst bnds rhs)
  | .ctx _ _ => none

/-- The base-rewrite reducts of a term in a presentation: every result of applying a premise-free
    rewrite whose left-hand side matches at the top level. -/
def baseReducts (p : Presentation) (t : AST) : List AST :=
  p.rewrites.filterMap (fun rd => applyBaseRewrite rd t)

end MeTTaIL
