/-
Module: MeTTaIL.Semantics.Hypercube
Layer: Semantics
Purpose: The finite sort-assignment core of the modal and spatial hypercube construction.
  A generated modal or spatial type family has a finite set of sort slots. In the equation-free case,
  every slot assignment is allowed. When the source theory has equations, the allowed vertices are the
  assignments whose induced two-sort algebra makes both sides of every equation evaluate to the same
  sort. This file records that finite checker and proves that membership in the computed center is
  exactly the semantic equation condition it is meant to decide.
Imports: MeTTaIL.Theory.Ops
Trusted boundary: none
Main exports: Hypercube.SortCode, Hypercube.SortExpr, Hypercube.Equation,
  Hypercube.InEquationalCenter, Hypercube.equationalCenter,
  Hypercube.mem_equationalCenter_iff, Hypercube.ModalSite, Hypercube.SpatialHead,
  AST.hypercubeSubterms, RewriteDecl.modalSites, Presentation.modalSites,
  Rule.spatialHead, Presentation.spatialHeads
Open obligations: generate the concrete modal and spatial slot families from `Presentation.terms`,
  `Presentation.equations`, and base-rewrite contexts, then feed them to this center checker.
-/
import MeTTaIL.Theory.Ops

namespace MeTTaIL
namespace Hypercube

universe u v

/-- The two sort choices used by the generated hypercube. -/
inductive SortCode where
  | star
  | box
  deriving DecidableEq, Repr

/-- A sort assignment gives every generated slot a sort. -/
abbrev SortAssignment (Slot : Type u) := Slot → SortCode

/-- A constructor head knows which output slot is read for a tuple of input sorts. -/
structure Head (Slot : Type u) where
  arity : Nat
  outputSlot : List SortCode → Slot

namespace Head

/-- The sort-level operation induced by a concrete assignment. -/
def sortOp {Slot : Type u} (σ : SortAssignment Slot) (h : Head Slot)
    (args : List SortCode) : SortCode :=
  σ (h.outputSlot args)

end Head

/-- Sort expressions are terms over variables and generated constructor heads. -/
inductive SortExpr (Head : Type u) (Var : Type v) where
  | var : Var → SortExpr Head Var
  | app : Head → List (SortExpr Head Var) → SortExpr Head Var

namespace SortExpr

mutual
  /-- Evaluate a sort expression in a two-sort algebra. -/
  def eval {Head : Type u} {Var : Type v} (op : Head → List SortCode → SortCode)
      (env : Var → SortCode) : SortExpr Head Var → SortCode
    | .var v => env v
    | .app h args => op h (evalList op env args)

  /-- Evaluate a list of sort expressions. -/
  def evalList {Head : Type u} {Var : Type v} (op : Head → List SortCode → SortCode)
      (env : Var → SortCode) : List (SortExpr Head Var) → List SortCode
    | [] => []
    | arg :: args => eval op env arg :: evalList op env args
end

end SortExpr

/-- A finite environment for the variables of one equation. Missing variables default to `star`. -/
def lookupSort {Var : Type v} [DecidableEq Var] (env : List (Var × SortCode))
    (v : Var) : SortCode :=
  match env with
  | [] => .star
  | (w, s) :: rest => if w = v then s else lookupSort rest v

/-- All boolean valuations of a finite list of variables. -/
def valuations {Var : Type v} : List Var → List (List (Var × SortCode))
  | [] => [[]]
  | v :: vars =>
      (valuations vars).flatMap fun env =>
        [(v, SortCode.star) :: env, (v, SortCode.box) :: env]

/-- A finite equation between sort expressions, with the variables to quantify over. -/
structure Equation (Head : Type u) (Var : Type v) where
  vars : List Var
  lhs : SortExpr Head Var
  rhs : SortExpr Head Var

namespace Equation

/-- One equation holds under one finite valuation. -/
def holdsOn {Head : Type u} {Var : Type v} [DecidableEq Var]
    (op : Head → List SortCode → SortCode) (e : Equation Head Var)
    (env : List (Var × SortCode)) : Prop :=
  e.lhs.eval op (lookupSort env) = e.rhs.eval op (lookupSort env)

/-- The boolean check for one valuation. -/
def checksOn {Head : Type u} {Var : Type v} [DecidableEq Var]
    (op : Head → List SortCode → SortCode) (e : Equation Head Var)
    (env : List (Var × SortCode)) : Bool :=
  if e.lhs.eval op (lookupSort env) = e.rhs.eval op (lookupSort env) then true else false

/-- The boolean valuation check says exactly that the equation holds under that valuation. -/
theorem checksOn_iff {Head : Type u} {Var : Type v} [DecidableEq Var]
    (op : Head → List SortCode → SortCode) (e : Equation Head Var)
    (env : List (Var × SortCode)) :
    e.checksOn op env = true ↔ e.holdsOn op env := by
  unfold checksOn holdsOn
  by_cases h : SortExpr.eval op (lookupSort env) e.lhs =
      SortExpr.eval op (lookupSort env) e.rhs
  · simp [h]
  · simp [h]

/-- The semantic center condition for one equation. -/
def InCenter {Head : Type u} {Var : Type v} [DecidableEq Var]
    (op : Head → List SortCode → SortCode) (e : Equation Head Var) : Prop :=
  ∀ env, env ∈ valuations e.vars → e.holdsOn op env

/-- The finite checker for one equation. -/
def admissible {Head : Type u} {Var : Type v} [DecidableEq Var]
    (op : Head → List SortCode → SortCode) (e : Equation Head Var) : Bool :=
  (valuations e.vars).all fun env => e.checksOn op env

/-- The equation checker accepts exactly the assignments that satisfy the finite semantic condition. -/
theorem admissible_iff {Head : Type u} {Var : Type v} [DecidableEq Var]
    (op : Head → List SortCode → SortCode) (e : Equation Head Var) :
    e.admissible op = true ↔ e.InCenter op := by
  constructor
  · intro h env henv
    exact (checksOn_iff op e env).1 ((List.all_eq_true.1 h) env henv)
  · intro h
    exact List.all_eq_true.2 fun env henv => (checksOn_iff op e env).2 (h env henv)

end Equation

/-- All listed equations hold for one induced sort algebra. -/
def InEquationalCenter {Head : Type u} {Var : Type v} [DecidableEq Var]
    (op : Head → List SortCode → SortCode) (eqns : List (Equation Head Var)) : Prop :=
  ∀ e, e ∈ eqns → e.InCenter op

/-- The boolean membership test for the equational center. -/
def centerMember {Head : Type u} {Var : Type v} [DecidableEq Var]
    (op : Head → List SortCode → SortCode) (eqns : List (Equation Head Var)) : Bool :=
  eqns.all fun e => e.admissible op

/-- The center membership test is equivalent to the semantic condition over all listed equations. -/
theorem centerMember_iff {Head : Type u} {Var : Type v} [DecidableEq Var]
    (op : Head → List SortCode → SortCode) (eqns : List (Equation Head Var)) :
    centerMember op eqns = true ↔ InEquationalCenter op eqns := by
  constructor
  · intro h e he
    exact (Equation.admissible_iff op e).1 ((List.all_eq_true.1 h) e he)
  · intro h
    exact List.all_eq_true.2 fun e he => (Equation.admissible_iff op e).2 (h e he)

/-- The raw vertices of a finite hypercube, represented as total assignments over slots. -/
def assignments {Slot : Type u} [DecidableEq Slot] (slots : List Slot) :
    List (SortAssignment Slot) :=
  (valuations slots).map fun env => lookupSort env

/-- The assignments that survive every equation. -/
def equationalCenter {Slot : Type u} {Var : Type v} [DecidableEq Slot] [DecidableEq Var]
    (slots : List Slot) (eqns : List (Equation (Head Slot) Var)) :
    List (SortAssignment Slot) :=
  (assignments slots).filter fun σ => centerMember (Head.sortOp σ) eqns

/-- Computed center membership is exactly raw-vertex membership plus the equation condition. -/
theorem mem_equationalCenter_iff {Slot : Type u} {Var : Type v}
    [DecidableEq Slot] [DecidableEq Var]
    (slots : List Slot) (eqns : List (Equation (Head Slot) Var))
    (σ : SortAssignment Slot) :
    σ ∈ equationalCenter slots eqns ↔
      σ ∈ assignments slots ∧ InEquationalCenter (Head.sortOp σ) eqns := by
  rw [equationalCenter, List.mem_filter]
  constructor
  · intro h
    exact ⟨h.1, (centerMember_iff (Head.sortOp σ) eqns).1 h.2⟩
  · intro h
    exact ⟨h.1, (centerMember_iff (Head.sortOp σ) eqns).2 h.2⟩

/-- Every computed center member satisfies all equations. -/
theorem equationalCenter_sound {Slot : Type u} {Var : Type v}
    [DecidableEq Slot] [DecidableEq Var]
    {slots : List Slot} {eqns : List (Equation (Head Slot) Var)}
    {σ : SortAssignment Slot} (h : σ ∈ equationalCenter slots eqns) :
    InEquationalCenter (Head.sortOp σ) eqns :=
  ((mem_equationalCenter_iff slots eqns σ).1 h).2

/-- Every raw assignment satisfying all equations is retained by the checker. -/
theorem equationalCenter_complete {Slot : Type u} {Var : Type v}
    [DecidableEq Slot] [DecidableEq Var]
    {slots : List Slot} {eqns : List (Equation (Head Slot) Var)}
    {σ : SortAssignment Slot} (hraw : σ ∈ assignments slots)
    (hcenter : InEquationalCenter (Head.sortOp σ) eqns) :
    σ ∈ equationalCenter slots eqns :=
  (mem_equationalCenter_iff slots eqns σ).2 ⟨hraw, hcenter⟩

/-- With no equations, the equational center is the whole raw hypercube. -/
theorem equationalCenter_nil {Slot : Type u} {Var : Type v}
    [DecidableEq Slot] [DecidableEq Var] (slots : List Slot) :
    equationalCenter (Var := Var) slots [] = assignments slots := by
  simp [equationalCenter, centerMember]

/-- One step in an AST position. -/
inductive PositionStep where
  | arg (index : Nat)
  | substBody
  | substRepl
  deriving DecidableEq, Repr

/-- A position in an AST, stored from the root toward the chosen subterm. -/
abbrev Position := List PositionStep

namespace Position

/-- Whether a position is the root of the term. -/
def isRoot (p : Position) : Bool :=
  p.isEmpty

end Position

end Hypercube

namespace DottedPath

/-- The variable name used by the hypercube site extractor. -/
def hypercubeName (p : DottedPath) : String :=
  p.baseName

end DottedPath

namespace AST

/-- Free base variable names in a term, without multiplicity cleanup. -/
def hypercubeVars : AST → List String
  | .var path => [path.hypercubeName]
  | .sexp _ args => args.flatMap hypercubeVars
  | .subst body repl _ => hypercubeVars body ++ hypercubeVars repl

/-- Free base variable names in all arguments except the one at `index`. -/
def hypercubeVarsExceptAt (index : Nat) (args : List AST) : List String :=
  ((List.range args.length).zip args).flatMap fun item =>
    if item.1 = index then [] else item.2.hypercubeVars

mutual
  /-- All subterms of a term, paired with their root-to-subterm positions. -/
  def hypercubeSubterms : AST → List (Hypercube.Position × AST)
    | t@(.var _) => [([], t)]
    | t@(.sexp _ args) => ([], t) :: hypercubeSubtermsArgs 0 args
    | t@(.subst body repl _) =>
        ([], t) ::
          (body.hypercubeSubterms.map fun sub =>
            (Hypercube.PositionStep.substBody :: sub.1, sub.2)) ++
          (repl.hypercubeSubterms.map fun sub =>
            (Hypercube.PositionStep.substRepl :: sub.1, sub.2))

  /-- All subterms of constructor arguments, with positions prefixed by their argument index. -/
  def hypercubeSubtermsArgs (start : Nat) : List AST → List (Hypercube.Position × AST)
    | [] => []
    | arg :: args =>
        (arg.hypercubeSubterms.map fun sub =>
          (Hypercube.PositionStep.arg start :: sub.1, sub.2)) ++
        hypercubeSubtermsArgs (start + 1) args
end

/-- Variables visible in the one-hole context at a position. -/
def hypercubeContextVarsAt? : Hypercube.Position → AST → Option (List String)
  | [], _ => some []
  | Hypercube.PositionStep.arg index :: rest, .sexp _ args =>
      match args[index]? with
      | none => none
      | some arg =>
          match arg.hypercubeContextVarsAt? rest with
          | none => none
          | some inner => some (inner ++ hypercubeVarsExceptAt index args)
  | Hypercube.PositionStep.substBody :: rest, .subst body repl _ =>
      match body.hypercubeContextVarsAt? rest with
      | none => none
      | some inner => some (inner ++ repl.hypercubeVars)
  | Hypercube.PositionStep.substRepl :: rest, .subst body repl _ =>
      match repl.hypercubeContextVarsAt? rest with
      | none => none
      | some inner => some (inner ++ body.hypercubeVars)
  | _ :: _, _ => none

/-- The root context has no variables outside the selected term. -/
theorem hypercubeContextVarsAt?_root (t : AST) :
    hypercubeContextVarsAt? [] t = some [] := by
  rfl

/-- Every term appears as its own root subterm. -/
theorem mem_hypercubeSubterms_root (t : AST) :
    ([], t) ∈ t.hypercubeSubterms := by
  cases t <;> simp [hypercubeSubterms]

end AST

namespace Hypercube

/-- A rewrite-left-hand-side subterm that can generate a rely-possibly modal type. -/
structure ModalSite where
  rewriteName : String
  position : Position
  subterm : AST
  contextVars : List String

/-- A constructor head that can generate a spatial type former. -/
structure SpatialHead where
  label : Label
  outputSort : Cat
  inputSorts : List Cat

end Hypercube

namespace RewriteDecl

/-- Modal sites generated by the subterms of a rewrite's left-hand side. -/
def modalSites (rd : RewriteDecl) : List Hypercube.ModalSite :=
  let lhs := rd.rw.conclusion.fst
  lhs.hypercubeSubterms.filterMap fun site =>
    match lhs.hypercubeContextVarsAt? site.1 with
    | none => none
    | some vars =>
        some (⟨rd.name, site.1, site.2, distinct vars⟩ : Hypercube.ModalSite)

/-- Proper modal sites skip the root and keep only strict subterms of the left-hand side. -/
def properModalSites (rd : RewriteDecl) : List Hypercube.ModalSite :=
  rd.modalSites.filter fun site => !site.position.isRoot

end RewriteDecl

namespace Item

/-- The argument carrier supplied by one grammar item when it contributes an AST child. -/
def hypercubeInputCat? : Item → Option Cat
  | .terminal _ => none
  | .nterminal c => some c
  | .bindNTerminal _ c => some c
  | .absNTerminal _ item => hypercubeInputCat? item

end Item

namespace Rule

/-- The argument carriers of a constructor, used for its spatial type family. -/
def hypercubeInputCats (r : Rule) : List Cat :=
  r.items.filterMap Item.hypercubeInputCat?

/-- The spatial head generated by one presentation term constructor. -/
def spatialHead (r : Rule) : Hypercube.SpatialHead where
  label := r.label
  outputSort := r.cat
  inputSorts := r.hypercubeInputCats

end Rule

namespace Presentation

/-- All modal sites generated from a presentation's rewrite left-hand sides. -/
def modalSites (p : Presentation) : List Hypercube.ModalSite :=
  p.rewrites.flatMap RewriteDecl.modalSites

/-- All strict-subterm modal sites generated from a presentation's rewrite left-hand sides. -/
def properModalSites (p : Presentation) : List Hypercube.ModalSite :=
  p.rewrites.flatMap RewriteDecl.properModalSites

/-- All spatial heads generated from a presentation's term constructors. -/
def spatialHeads (p : Presentation) : List Hypercube.SpatialHead :=
  p.terms.map Rule.spatialHead

end Presentation

end MeTTaIL
