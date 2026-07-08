-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Syntax
Layer: Syntax
Purpose: The data model of theory presentations, the object syntax that `.module` programs build and
  elaborate to. These types mirror the Scala `BasePres` and the BNFC abstract syntax of MeTTaIL
  (package `io.f1r3fly.mettail`, grammar `GSLT/src/main/bnfc/metta_venus.cf`), with Lean names matching
  the Scala constructs so the correspondence is auditable. The layer is computable and does not import
  Mathlib, so it runs. Structural equality follows the Scala `.equals`, mirrored with `BEq`. The types
  that nest through `List` (`Cat` via `prod`, `AST` via `sexp`, `Presentation` via `references`) get a
  hand-written `BEq` by mutual recursion because Lean's `deriving` does not support that nesting (lean4
  issue #7580); the non-nested types derive it.
Imports: none (Mathlib-free)
Trusted boundary: human-reviewed spec
Main exports: DottedPath, Cat, Label, Item, Rule, AST, Equation, Hyp, Rewrite, RewriteDecl, Presentation
Open obligations: none
-/

namespace MeTTaIL

/-- A dotted path of identifiers, e.g. `a.b.c`. Mirrors BNFC `DottedPath`
    (`BaseDottedPath Ident | QualifiedDottedPath Ident DottedPath`). -/
inductive DottedPath where
  | base (ident : String)
  | qualified (ident : String) (rest : DottedPath)
deriving Inhabited, BEq, DecidableEq, Repr

/-- A sort / category, i.e. an arity expression. The arity language is the generating shapes closed
    under lists, exponentials (`arrow`), and products. Mirrors BNFC `Cat`
    (`IdCat | ListOfCat | ArrowCat | ProdCat`). -/
inductive Cat where
  | idCat (name : String)
  | listOf (c : Cat)
  | arrow (dom cod : Cat)
  | prod (cs : List Cat)
deriving Inhabited

mutual
  /-- Structural equality on categories, the analogue of the Scala `Cat.equals`. Hand-written
      because `Cat` nests through `List Cat` in `prod`, which `deriving BEq` does not support. -/
  def Cat.beq : Cat → Cat → Bool
    | .idCat a,   .idCat b   => a == b
    | .listOf a,  .listOf b  => Cat.beq a b
    | .arrow a b, .arrow c d => Cat.beq a c && Cat.beq b d
    | .prod cs,   .prod ds   => Cat.beqList cs ds
    | _,          _          => false
  /-- Pointwise structural equality on category lists (the `prod` arguments). -/
  def Cat.beqList : List Cat → List Cat → Bool
    | [],      []      => true
    | c :: cs, d :: ds => Cat.beq c d && Cat.beqList cs ds
    | _,       _       => false
end

instance : BEq Cat := ⟨Cat.beq⟩

/-- A constructor label. Mirrors BNFC `Label` (`Id | Wild | ListE | ListCons | ListOne`). The list
    labels carry the element category of the list sort they construct. -/
inductive Label where
  | id (name : String)
  | wild
  | listE (c : Cat)
  | listCons (c : Cat)
  | listOne (c : Cat)
deriving Inhabited, BEq

/-- One item in a function symbol's concrete syntax. Mirrors BNFC `Item`. `terminal` is a literal;
    `nterminal` is a sort argument; `absNTerminal x it` is the abstraction `(x) it` with `x` bound in
    `it`; `bindNTerminal x c` is `(Bind x c)`. The `absNTerminal`/`bindNTerminal` pair encodes a
    higher-order (exponential) argument. -/
inductive Item where
  | terminal (s : String)
  | nterminal (c : Cat)
  | absNTerminal (x : String) (it : Item)
  | bindNTerminal (x : String) (c : Cat)
deriving Inhabited, BEq

/-- A function symbol, written as a grammar rule `label . cat ::= items`. `cat` is the output arity;
    the input arity is read off the non-terminal items. Mirrors BNFC `Rule . Def`. -/
structure Rule where
  label : Label
  cat : Cat
  items : List Item
deriving Inhabited, BEq

/-- A term. Mirrors BNFC `AST`: `var` is a (possibly qualified) variable, `sexp label args` is an
    applied constructor `(label args...)`, and `subst body repl v` is the built-in capture-avoiding
    substitution `(Subst body repl v)` that drives the COMM rule. -/
inductive AST where
  | var (path : DottedPath)
  | sexp (label : Label) (args : List AST)
  | subst (body repl : AST) (v : DottedPath)
deriving Inhabited

mutual
  /-- Structural equality on terms, the analogue of the Scala `AST.equals`. Hand-written because
      `AST` nests through `List AST` in `sexp`. -/
  def AST.beq : AST → AST → Bool
    | .var p,       .var q            => p == q
    | .sexp l cs,   .sexp m ds        => l == m && AST.beqList cs ds
    | .subst b r v, .subst b' r' v'   => AST.beq b b' && AST.beq r r' && v == v'
    | _,            _                 => false
  /-- Pointwise structural equality on term lists (the `sexp` arguments). -/
  def AST.beqList : List AST → List AST → Bool
    | [],      []      => true
    | c :: cs, d :: ds => AST.beq c d && AST.beqList cs ds
    | _,       _       => false
end

instance : BEq AST := ⟨AST.beq⟩

/-- An equation, optionally guarded by a freshness side condition `if x # y then ...`. Mirrors BNFC
    `Equation` (`EquationImpl | EquationFresh`). -/
inductive Equation where
  | impl (lhs rhs : AST)
  | fresh (x y : String) (e : Equation)
deriving Inhabited, BEq

/-- A rewrite premise `src ~> tgt` over dotted-path variables. Mirrors BNFC `Hyp . Hypothesis`. -/
structure Hyp where
  src : DottedPath
  tgt : DottedPath
deriving Inhabited, BEq

/-- A rewrite rule: a conclusion `lhs ~> rhs`, optionally under premises `let h in ...`. Mirrors
    BNFC `Rewrite` (`RewriteBase | RewriteContext`). -/
inductive Rewrite where
  | base (lhs rhs : AST)
  | ctx (h : Hyp) (r : Rewrite)
deriving Inhabited, BEq

/-- A named rewrite declaration `name : rw`. Mirrors BNFC `RDecl . RewriteDecl`. -/
structure RewriteDecl where
  name : String
  rw : Rewrite
deriving Inhabited, BEq

/-- A theory presentation, the in-memory `BasePres`: exported sorts, function symbols (terms),
    equations, rewrites, and a references map (declared prefix to sub-presentation) used to validate
    dotted-path prefixes in rewrites.

    The `references` field makes the type recursive, exactly as `BasePres.listmapentry_` does
    (`MakeMapEntry . MapEntry ::= Ident "=>" Pres`). Our `elaborate` never populates it, so every
    presentation this development produces has empty references; the field is kept to mirror `BasePres`
    faithfully, where a literal presentation can carry references. The type is an `inductive` rather
    than a `structure` because Lean structures may not be recursive; named accessors are defined just
    below. -/
inductive Presentation where
  | mk (exports : List Cat) (terms : List Rule) (equations : List Equation)
       (rewrites : List RewriteDecl) (references : List (String × Presentation))
deriving Inhabited

mutual
  /-- Structural equality on presentations. Hand-written because `Presentation` nests through
      `List (String × Presentation)` in `references`. -/
  def Presentation.beq : Presentation → Presentation → Bool
    | .mk e₁ t₁ q₁ r₁ m₁, .mk e₂ t₂ q₂ r₂ m₂ =>
        e₁ == e₂ && t₁ == t₂ && q₁ == q₂ && r₁ == r₂ && Presentation.beqRefs m₁ m₂
  /-- Pointwise structural equality on reference maps. -/
  def Presentation.beqRefs :
      List (String × Presentation) → List (String × Presentation) → Bool
    | [],           []           => true
    | (s, p) :: m₁, (t, q) :: m₂ => s == t && Presentation.beq p q && Presentation.beqRefs m₁ m₂
    | _,            _            => false
end

instance : BEq Presentation := ⟨Presentation.beq⟩

namespace Presentation

/-- The exported sorts of a presentation (the generating shapes `S`). -/
def exports : Presentation → List Cat
  | mk e _ _ _ _ => e

/-- The function symbols of a presentation (the set `F`, written as grammar rules). -/
def terms : Presentation → List Rule
  | mk _ t _ _ _ => t

/-- The equations of a presentation (the set `E`). -/
def equations : Presentation → List Equation
  | mk _ _ q _ _ => q

/-- The named rewrite rules of a presentation (the GSLT reduction rules). -/
def rewrites : Presentation → List RewriteDecl
  | mk _ _ _ r _ => r

/-- The references map of a presentation (declared prefix to sub-presentation). -/
def references : Presentation → List (String × Presentation)
  | mk _ _ _ _ m => m

/-- The empty presentation: no exports, terms, equations, rewrites, or references. Mirrors
    `BasePresOps.empty`. -/
def empty : Presentation := mk [] [] [] [] []

end Presentation

end MeTTaIL
