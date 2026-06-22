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
  Hypercube.Slot, Hypercube.SlotFamily, Hypercube.ModalSite.slotFamily,
  Hypercube.SpatialHead.slotFamily, Hypercube.SlotConstraint,
  Hypercube.constrainedCenter, Hypercube.TypeFamily, Hypercube.RuleKind,
  Hypercube.RuleScheme, Hypercube.ModalSite.ruleSchemes,
  Hypercube.SpatialHead.ruleSchemes, Hypercube.JudgmentFootprint,
  Hypercube.RuleScheme.footprints,
  AST.hypercubeSubterms, RewriteDecl.modalSites, Presentation.modalSites,
  Rule.spatialHead, Presentation.spatialHeads, Presentation.hypercubeSlotFamilies,
  Presentation.hypercubeSlots, Presentation.hypercubeTypeFamilies,
  Presentation.hypercubeRuleSchemes, Presentation.hypercubeJudgmentFootprints,
  Presentation.hypercubeConstrainedCenter
Open obligations: interpret these judgment footprints as full typing rules, generate the sort-level
  equations from those judgments, then feed the resulting equations to this center checker.
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
  deriving BEq, DecidableEq, Repr

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

/-- A stable identifier for a generated modal site. -/
structure SiteId where
  rewriteName : String
  position : Position
  deriving BEq, DecidableEq, Repr

/-- A rewrite-left-hand-side subterm that can generate a rely-possibly modal type. -/
structure ModalSite where
  rewriteName : String
  position : Position
  subterm : AST
  contextVars : List String

/-- The stable identifier of a modal site. -/
def ModalSite.siteId (site : ModalSite) : SiteId where
  rewriteName := site.rewriteName
  position := site.position

/-- A constructor head that can generate a spatial type former. -/
structure SpatialHead where
  label : Label
  outputSort : Cat
  inputSorts : List Cat

/-- One sort slot in the generated hypercube. -/
inductive Slot where
  | modalRely (site : SiteId) (name : String)
  | modalOutput (site : SiteId)
  | spatialArg (head : String) (index : Nat)
  | spatialOutput (head : String)
  deriving BEq, DecidableEq, Repr

namespace Slot

/-- A nullary sort-level head that reads this slot. -/
def head (slot : Slot) : Head Slot where
  arity := 0
  outputSlot := fun _ => slot

/-- This nullary head reads exactly this slot. -/
theorem head_sortOp_eq (slot : Slot) (σ : SortAssignment Slot) (args : List SortCode) :
    Head.sortOp σ slot.head args = σ slot := by
  rfl

/-- The sort expression that reads this slot. -/
def sortExpr (slot : Slot) : SortExpr (Head Slot) Unit :=
  .app slot.head []

/-- Evaluating a slot expression returns the assigned sort of that slot. -/
theorem sortExpr_eval_eq (slot : Slot) (σ : SortAssignment Slot)
    (env : Unit → SortCode) :
    slot.sortExpr.eval (Head.sortOp σ) env = σ slot := by
  rfl

end Slot

/-- A generated sort constraint that says two slots must receive the same sort. -/
structure SlotConstraint where
  lhs : Slot
  rhs : Slot
  deriving BEq, DecidableEq, Repr

namespace SlotConstraint

/-- The generic center-checker equation for this slot equality. -/
def toEquation (c : SlotConstraint) : Equation (Head Slot) Unit where
  vars := []
  lhs := c.lhs.sortExpr
  rhs := c.rhs.sortExpr

/-- A slot constraint holds for one sort assignment. -/
def holds (σ : SortAssignment Slot) (c : SlotConstraint) : Prop :=
  σ c.lhs = σ c.rhs

/-- The generic equation view is equivalent to direct slot equality. -/
theorem toEquation_inCenter_iff (c : SlotConstraint) (σ : SortAssignment Slot) :
    c.toEquation.InCenter (Head.sortOp σ) ↔ c.holds σ := by
  constructor
  · intro h
    have hholds := h [] (by simp [toEquation, valuations])
    simpa [toEquation, holds, Equation.holdsOn, Slot.sortExpr, Slot.head,
      Head.sortOp, SortExpr.eval, SortExpr.evalList] using hholds
  · intro h env henv
    simpa [toEquation, holds, Equation.holdsOn, Slot.sortExpr, Slot.head,
      Head.sortOp, SortExpr.eval] using h

end SlotConstraint

/-- All slot constraints hold for one sort assignment. -/
def InSlotConstraintCenter (σ : SortAssignment Slot) (constraints : List SlotConstraint) : Prop :=
  ∀ c, c ∈ constraints → c.holds σ

/-- The generic equation center agrees with direct slot-constraint satisfaction. -/
theorem inEquationalCenter_slotConstraints_iff
    (σ : SortAssignment Slot) (constraints : List SlotConstraint) :
    InEquationalCenter (Head.sortOp σ) (constraints.map SlotConstraint.toEquation) ↔
      InSlotConstraintCenter σ constraints := by
  constructor
  · intro h c hc
    exact (SlotConstraint.toEquation_inCenter_iff c σ).1
      (h c.toEquation (List.mem_map.2 ⟨c, hc, rfl⟩))
  · intro h e he
    rcases List.mem_map.1 he with ⟨c, hc, rfl⟩
    exact (SlotConstraint.toEquation_inCenter_iff c σ).2 (h c hc)

/-- The center induced by explicit slot equalities. -/
def constrainedCenter (slots : List Slot) (constraints : List SlotConstraint) :
    List (SortAssignment Slot) :=
  equationalCenter slots (constraints.map SlotConstraint.toEquation)

/-- Membership in a constrained center is raw assignment plus direct satisfaction of each slot constraint. -/
theorem mem_constrainedCenter_iff (slots : List Slot) (constraints : List SlotConstraint)
    (σ : SortAssignment Slot) :
    σ ∈ constrainedCenter slots constraints ↔
      σ ∈ assignments slots ∧ InSlotConstraintCenter σ constraints := by
  rw [constrainedCenter, mem_equationalCenter_iff]
  constructor
  · intro h
    exact ⟨h.1, (inEquationalCenter_slotConstraints_iff σ constraints).1 h.2⟩
  · intro h
    exact ⟨h.1, (inEquationalCenter_slotConstraints_iff σ constraints).2 h.2⟩

/-- The slots carried by one generated modal or spatial type former. -/
structure SlotFamily where
  name : String
  inputSlots : List Slot
  outputSlot : Slot
  deriving Repr

namespace SlotFamily

/-- All slots of a generated type family. -/
def slots (family : SlotFamily) : List Slot :=
  family.inputSlots ++ [family.outputSlot]

/-- The output slot is part of the family. -/
theorem outputSlot_mem_slots (family : SlotFamily) :
    family.outputSlot ∈ family.slots := by
  simp [slots]

/-- The sort-level head read by the center checker. -/
def head (family : SlotFamily) : Head Slot where
  arity := family.inputSlots.length
  outputSlot := fun _ => family.outputSlot

/-- This generated head reads the family's output slot. -/
theorem head_sortOp_eq (family : SlotFamily) (σ : SortAssignment Slot) (args : List SortCode) :
    Head.sortOp σ family.head args = σ family.outputSlot := by
  rfl

end SlotFamily

end Hypercube

namespace Cat

/-- A printable key used for generated hypercube slot names. -/
def hypercubeKey : Cat → String
  | .idCat name => name
  | .listOf c => "List(" ++ c.hypercubeKey ++ ")"
  | .arrow dom cod => "Arrow(" ++ dom.hypercubeKey ++ "," ++ cod.hypercubeKey ++ ")"
  | .prod cs => "Prod(" ++ ",".intercalate (cs.map hypercubeKey) ++ ")"

end Cat

namespace Label

/-- A printable key used for generated hypercube slot names. -/
def hypercubeKey : Label → String
  | .id name => name
  | .wild => "_"
  | .listE c => "ListE(" ++ c.hypercubeKey ++ ")"
  | .listCons c => "ListCons(" ++ c.hypercubeKey ++ ")"
  | .listOne c => "ListOne(" ++ c.hypercubeKey ++ ")"

end Label

namespace Hypercube

namespace ModalSite

/-- The slot family generated by this modal site. -/
def slotFamily (site : ModalSite) : SlotFamily where
  name := site.rewriteName
  inputSlots := site.contextVars.map fun name => Slot.modalRely site.siteId name
  outputSlot := Slot.modalOutput site.siteId

/-- Modal sites contribute one slot per rely variable, plus one output slot. -/
theorem slotFamily_slots_length (site : ModalSite) :
    site.slotFamily.slots.length = site.contextVars.length + 1 := by
  simp [slotFamily, SlotFamily.slots]

/-- The modal output slot is part of the generated family. -/
theorem outputSlot_mem_slotFamily (site : ModalSite) :
    site.slotFamily.outputSlot ∈ site.slotFamily.slots :=
  SlotFamily.outputSlot_mem_slots site.slotFamily

end ModalSite

namespace SpatialHead

/-- The printable key of a spatial head. -/
def key (head : SpatialHead) : String :=
  head.label.hypercubeKey

/-- The slot family generated by this spatial head. -/
def slotFamily (head : SpatialHead) : SlotFamily where
  name := head.key
  inputSlots := (List.range head.inputSorts.length).map fun index =>
    Slot.spatialArg head.key index
  outputSlot := Slot.spatialOutput head.key

/-- Spatial heads contribute one slot per constructor input, plus one output slot. -/
theorem slotFamily_slots_length (head : SpatialHead) :
    head.slotFamily.slots.length = head.inputSorts.length + 1 := by
  simp [slotFamily, SlotFamily.slots]

/-- The spatial output slot is part of the generated family. -/
theorem outputSlot_mem_slotFamily (head : SpatialHead) :
    head.slotFamily.outputSlot ∈ head.slotFamily.slots :=
  SlotFamily.outputSlot_mem_slots head.slotFamily

end SpatialHead

/-- The source of a generated hypercube type family. -/
inductive FamilyKind where
  | modal
  | spatial
  deriving DecidableEq, Repr

/-- A generated modal or spatial type family before its typing judgment is interpreted. -/
inductive TypeFamily where
  | modal (site : ModalSite)
  | spatial (head : SpatialHead)

namespace TypeFamily

/-- Whether this generated family came from a rewrite site or a constructor head. -/
def kind : TypeFamily → FamilyKind
  | .modal _ => .modal
  | .spatial _ => .spatial

/-- The slots read by this generated family. -/
def slotFamily : TypeFamily → SlotFamily
  | .modal site => site.slotFamily
  | .spatial head => head.slotFamily

/-- Modal generated families use the modal site's slots. -/
theorem slotFamily_modal (site : ModalSite) :
    (TypeFamily.modal site).slotFamily = site.slotFamily := by
  rfl

/-- Spatial generated families use the constructor head's slots. -/
theorem slotFamily_spatial (head : SpatialHead) :
    (TypeFamily.spatial head).slotFamily = head.slotFamily := by
  rfl

end TypeFamily

/-- A generated rule surface associated with one hypercube family. -/
inductive RuleKind where
  | formation
  | introduction
  | elimination
  | eliminationStep
  | reductTyping
  | laxConversion
  deriving DecidableEq, Repr

/-- A generated judgment shape that reads slots from a rule scheme. -/
inductive JudgmentKind where
  | relySorts
  | argumentSorts
  | targetSort
  | familySort
  | subjectTyping
  | reductTyping
  | relyInhabitants
  | argumentInhabitants
  | rewriteStep
  | diamondTyping
  | structuralMotive
  deriving DecidableEq, Repr

/-- The slot footprint of one generated judgment premise or conclusion. -/
structure JudgmentFootprint where
  kind : JudgmentKind
  slots : List Slot
  deriving Repr

namespace JudgmentFootprint

/-- A footprint stays within the slots of a generated family. -/
def within (family : SlotFamily) (fp : JudgmentFootprint) : Prop :=
  ∀ slot, slot ∈ fp.slots → slot ∈ family.slots

end JudgmentFootprint

namespace SlotFamily

/-- A generated judgment that reads all input slots of a family. -/
def inputFootprint (family : SlotFamily) (kind : JudgmentKind) : JudgmentFootprint where
  kind := kind
  slots := family.inputSlots

/-- A generated judgment that reads the output slot of a family. -/
def outputFootprint (family : SlotFamily) (kind : JudgmentKind) : JudgmentFootprint where
  kind := kind
  slots := [family.outputSlot]

/-- A generated judgment that reads every slot of a family. -/
def allFootprint (family : SlotFamily) (kind : JudgmentKind) : JudgmentFootprint where
  kind := kind
  slots := family.slots

/-- Input-slot footprints stay within their family. -/
theorem inputFootprint_within (family : SlotFamily) (kind : JudgmentKind) :
    (family.inputFootprint kind).within family := by
  intro slot hslot
  exact List.mem_append_left [family.outputSlot] hslot

/-- Output-slot footprints stay within their family. -/
theorem outputFootprint_within (family : SlotFamily) (kind : JudgmentKind) :
    (family.outputFootprint kind).within family := by
  intro slot hslot
  simp [outputFootprint, slots] at hslot ⊢
  exact Or.inr hslot

/-- Whole-family footprints stay within their family. -/
theorem allFootprint_within (family : SlotFamily) (kind : JudgmentKind) :
    (family.allFootprint kind).within family := by
  intro slot hslot
  simpa [allFootprint] using hslot

end SlotFamily

/-- One rule scheme generated by a modal or spatial family. -/
structure RuleScheme where
  family : TypeFamily
  kind : RuleKind

namespace RuleScheme

/-- The slots read by this generated rule scheme. -/
def slotFamily (scheme : RuleScheme) : SlotFamily :=
  scheme.family.slotFamily

/-- Every generated rule scheme keeps the output slot of its family. -/
theorem outputSlot_mem_slotFamily (scheme : RuleScheme) :
    scheme.slotFamily.outputSlot ∈ scheme.slotFamily.slots :=
  SlotFamily.outputSlot_mem_slots scheme.slotFamily

/-- Whether this rule kind belongs to this kind of generated family. -/
def compatible : RuleScheme → Bool
  | ⟨_, .formation⟩ => true
  | ⟨_, .introduction⟩ => true
  | ⟨family, .eliminationStep⟩ => family.kind == .modal
  | ⟨family, .reductTyping⟩ => family.kind == .modal
  | ⟨family, .laxConversion⟩ => family.kind == .modal
  | ⟨family, .elimination⟩ => family.kind == .spatial

/-- The generated judgment footprints read by this rule scheme. Invalid family/kind pairs read none. -/
def footprints (scheme : RuleScheme) : List JudgmentFootprint :=
  let family := scheme.slotFamily
  match scheme.family.kind, scheme.kind with
  | .modal, .formation =>
      [family.inputFootprint .relySorts,
       family.outputFootprint .targetSort,
       family.outputFootprint .familySort]
  | .modal, .introduction =>
      [family.inputFootprint .relySorts,
       family.outputFootprint .targetSort,
       family.outputFootprint .reductTyping,
       family.outputFootprint .subjectTyping]
  | .modal, .eliminationStep =>
      [family.outputFootprint .subjectTyping,
       family.inputFootprint .relyInhabitants,
       family.allFootprint .rewriteStep]
  | .modal, .reductTyping =>
      [family.outputFootprint .subjectTyping,
       family.inputFootprint .relyInhabitants,
       family.outputFootprint .reductTyping]
  | .modal, .laxConversion =>
      [family.outputFootprint .subjectTyping,
       family.inputFootprint .relyInhabitants,
       family.outputFootprint .diamondTyping]
  | .spatial, .formation =>
      [family.inputFootprint .argumentSorts,
       family.outputFootprint .familySort]
  | .spatial, .introduction =>
      [family.inputFootprint .argumentSorts,
       family.inputFootprint .argumentInhabitants,
       family.outputFootprint .subjectTyping]
  | .spatial, .elimination =>
      [family.inputFootprint .argumentInhabitants,
       family.outputFootprint .subjectTyping,
       family.outputFootprint .structuralMotive]
  | _, _ => []

/-- The slots used by every footprint of a scheme are family slots. -/
theorem footprintSlots_subset_slots (scheme : RuleScheme) :
    ∀ slot, slot ∈ (scheme.footprints.flatMap JudgmentFootprint.slots) →
      slot ∈ scheme.slotFamily.slots := by
  cases scheme with
  | mk family kind =>
      cases family <;> cases kind <;>
        simp [footprints, TypeFamily.kind,
          SlotFamily.inputFootprint, SlotFamily.outputFootprint, SlotFamily.allFootprint,
          SlotFamily.slots]

/-- Every generated footprint stays within the scheme's family slots. -/
theorem footprints_within (scheme : RuleScheme) {fp : JudgmentFootprint}
    (hfp : fp ∈ scheme.footprints) :
    fp.within scheme.slotFamily := by
  intro slot hslot
  exact footprintSlots_subset_slots scheme slot
    (List.mem_flatMap.2 ⟨fp, hfp, hslot⟩)

end RuleScheme

namespace ModalSite

/-- Modal families generate formation, introduction, elimination-step, reduct-typing, and lax-conversion rules. -/
def ruleKinds : List RuleKind :=
  [.formation, .introduction, .eliminationStep, .reductTyping, .laxConversion]

/-- The modal rule-kind list has the five surfaces used in the generated-hypercubes draft. -/
theorem ruleKinds_length : ModalSite.ruleKinds.length = 5 := by
  rfl

/-- The rule schemes generated by this modal site. -/
def ruleSchemes (site : ModalSite) : List RuleScheme :=
  ModalSite.ruleKinds.map fun kind => { family := TypeFamily.modal site, kind := kind }

/-- Modal sites generate five rule schemes. -/
theorem ruleSchemes_length (site : ModalSite) :
    site.ruleSchemes.length = 5 := by
  simp [ruleSchemes, ruleKinds]

/-- Modal-site generation only emits modal-compatible rule schemes. -/
theorem ruleSchemes_compatible (site : ModalSite) {scheme : RuleScheme}
    (hscheme : scheme ∈ site.ruleSchemes) :
    scheme.compatible = true := by
  simp [ruleSchemes, ruleKinds, RuleScheme.compatible, TypeFamily.kind] at hscheme ⊢
  rcases hscheme with rfl | rfl | rfl | rfl | rfl <;> rfl

end ModalSite

namespace SpatialHead

/-- Spatial families generate formation, introduction, and elimination rules. -/
def ruleKinds : List RuleKind :=
  [.formation, .introduction, .elimination]

/-- The spatial rule-kind list has the three structural surfaces from the generated-hypercubes draft. -/
theorem ruleKinds_length : SpatialHead.ruleKinds.length = 3 := by
  rfl

/-- The rule schemes generated by this spatial head. -/
def ruleSchemes (head : SpatialHead) : List RuleScheme :=
  SpatialHead.ruleKinds.map fun kind => { family := TypeFamily.spatial head, kind := kind }

/-- Spatial heads generate three rule schemes. -/
theorem ruleSchemes_length (head : SpatialHead) :
    head.ruleSchemes.length = 3 := by
  simp [ruleSchemes, ruleKinds]

/-- Spatial-head generation only emits spatial-compatible rule schemes. -/
theorem ruleSchemes_compatible (head : SpatialHead) {scheme : RuleScheme}
    (hscheme : scheme ∈ head.ruleSchemes) :
    scheme.compatible = true := by
  simp [ruleSchemes, ruleKinds, RuleScheme.compatible, TypeFamily.kind] at hscheme ⊢
  rcases hscheme with rfl | rfl | rfl <;> rfl

end SpatialHead

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

/-- The generated modal and spatial slot families of a presentation. -/
def hypercubeSlotFamilies (p : Presentation) : List Hypercube.SlotFamily :=
  (p.properModalSites.map Hypercube.ModalSite.slotFamily) ++
  (p.spatialHeads.map Hypercube.SpatialHead.slotFamily)

/-- The generated slots of a presentation. -/
def hypercubeSlots (p : Presentation) : List Hypercube.Slot :=
  distinct (p.hypercubeSlotFamilies.flatMap Hypercube.SlotFamily.slots)

/-- The generated modal and spatial type families of a presentation. -/
def hypercubeTypeFamilies (p : Presentation) : List Hypercube.TypeFamily :=
  (p.properModalSites.map Hypercube.TypeFamily.modal) ++
  (p.spatialHeads.map Hypercube.TypeFamily.spatial)

/-- The generated modal and spatial rule schemes of a presentation. -/
def hypercubeRuleSchemes (p : Presentation) : List Hypercube.RuleScheme :=
  (p.properModalSites.flatMap Hypercube.ModalSite.ruleSchemes) ++
  (p.spatialHeads.flatMap Hypercube.SpatialHead.ruleSchemes)

/-- The generated judgment footprints of a presentation. -/
def hypercubeJudgmentFootprints (p : Presentation) : List Hypercube.JudgmentFootprint :=
  p.hypercubeRuleSchemes.flatMap Hypercube.RuleScheme.footprints

/-- The center of this presentation under explicit generated slot constraints. -/
def hypercubeConstrainedCenter (p : Presentation)
    (constraints : List Hypercube.SlotConstraint) :
    List (Hypercube.SortAssignment Hypercube.Slot) :=
  Hypercube.constrainedCenter p.hypercubeSlots constraints

end Presentation

end MeTTaIL
