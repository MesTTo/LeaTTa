-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.MorkMM2Lowering
Layer: Core
Purpose: A proof-facing lowering view for MORK MM2 `exec` atoms. It records the source-list and
  template-list modes recognized by the MORK bridge, classifies source factors and template effects,
  evaluates path/equality/inequality sources against the reference `Space`, applies main-space
  effects, and models priority selection over semantic exec rules.
Imports: MettaHyperonFull.Core.MorkMM2
Trusted boundary: none
Main exports: MorkMM2Lowering.ExecPlan, MorkMM2Lowering.lowerExec?,
  MorkMM2Lowering.applyPlan, MorkMM2Lowering.takeLowest, MorkMM2Lowering.stepByPriority
Open obligations: external non-ACT source and sink resources and the byte-level path ordering used by
  the concrete MORK trie remain implementation refinements above this pure model.
-/
import MettaHyperonFull.Core.MorkMM2

namespace Metta

namespace MorkMM2Lowering

/-- Which side of an `exec` term is being parsed. -/
inductive ListSide where
  | source
  | template
  deriving Repr, BEq, Inhabited

/-- Recognized list heads in MM2 source and template positions. -/
inductive ListMode where
  | conjunction
  | sourceList
  | outputList
  | other : Atom → ListMode
  deriving Repr, BEq, Inhabited

/-- A lowered source factor. Path-like sources contribute reference `Space` query patterns. -/
inductive SourceKind where
  | pathPattern : Atom → SourceKind
  | btm : Atom → SourceKind
  | act : Atom → Atom → SourceKind
  | equation : Atom → Atom → SourceKind
  | inequality : Atom → Atom → SourceKind
  | other : Atom → SourceKind
  deriving Repr, BEq, Inhabited

/-- A lowered template effect. Other effects are recorded but do not mutate the reference `Space`. -/
inductive TemplateEffect where
  | add : Atom → TemplateEffect
  | remove : Atom → TemplateEffect
  | act : Atom → Atom → TemplateEffect
  | other : Atom → TemplateEffect
  deriving Repr, BEq, Inhabited

/-- One source factor with its position in the source list. -/
structure LoweredSource where
  index : Nat
  term : Atom
  kind : SourceKind
  deriving Repr, BEq, Inhabited

/-- One template effect with the metadata used by the MORK planner. -/
structure LoweredEffect where
  index : Nat
  term : Atom
  kind : TemplateEffect
  bindingSensitive : Bool
  addsExec : Bool
  laterStepOutput : Bool
  deriving Repr, BEq, Inhabited

/-- Summary counters for one lowered `exec` atom. -/
structure ExecSummary where
  sources : Nat
  equationSources : Nat
  pathSources : Nat
  addEffects : Nat
  removeEffects : Nat
  actEffects : Nat
  bindingSensitiveEffects : Nat
  bindingInsensitiveEffects : Nat
  addedExecs : Nat
  laterStepOutputs : Nat
  deriving Repr, BEq, Inhabited

/-- Lowered view of one MM2 `exec` atom. -/
structure ExecPlan where
  root : Atom
  location : Atom
  sourceMode : ListMode
  templateMode : ListMode
  sources : List LoweredSource
  effects : List LoweredEffect
  summary : ExecSummary
  deriving Repr, BEq, Inhabited

/-- A reference-space mutation induced by a lowered template effect. -/
inductive SpaceOp where
  | add : Atom → SpaceOp
  | remove : Atom → SpaceOp
  deriving Repr, BEq, Inhabited

/-- Classify a source or template list head. -/
def listMode (side : ListSide) (head : Atom) : ListMode :=
  if head == Atom.sym "," then
    ListMode.conjunction
  else
    match side with
    | ListSide.source =>
        if head == Atom.sym "I" then ListMode.sourceList else ListMode.other head
    | ListSide.template =>
        if head == Atom.sym "O" then ListMode.outputList else ListMode.other head

/-- Extract the mode and children of a nonempty MM2 source or template list. -/
def listTerms? (side : ListSide) : Atom → Option (ListMode × List Atom)
  | Atom.expr (head :: rest) => some (listMode side head, rest)
  | _ => none

/-- Extract an MM2 source list. -/
def sourceTerms? (atom : Atom) : Option (ListMode × List Atom) :=
  listTerms? ListSide.source atom

/-- Extract an MM2 template list. -/
def templateTerms? (atom : Atom) : Option (ListMode × List Atom) :=
  listTerms? ListSide.template atom

/-- Classify one source factor. -/
def sourceKind : Atom → SourceKind
  | Atom.expr [] => SourceKind.other (Atom.expr [])
  | Atom.expr [Atom.sym "==", lhs, rhs] => SourceKind.equation lhs rhs
  | Atom.expr [Atom.sym "!=", lhs, rhs] => SourceKind.inequality lhs rhs
  | Atom.expr [Atom.sym "BTM", pattern] => SourceKind.btm pattern
  | Atom.expr [Atom.sym "ACT", name, pattern] => SourceKind.act name pattern
  | term => SourceKind.pathPattern term

/-- Classify one `O`-list effect term. -/
def outputEffectKind : Atom → TemplateEffect
  | Atom.expr [Atom.sym "+", term] => TemplateEffect.add term
  | Atom.expr [Atom.sym "-", term] => TemplateEffect.remove term
  | Atom.expr [Atom.sym "ACT", name, term] => TemplateEffect.act name term
  | term => TemplateEffect.other term

/-- Classify one template term under the already recognized list mode. -/
def templateKind (mode : ListMode) (term : Atom) : TemplateEffect :=
  match mode with
  | ListMode.conjunction => TemplateEffect.add term
  | ListMode.outputList => outputEffectKind term
  | _ => TemplateEffect.other term

namespace SourceKind

/-- The path-like query pattern for a lowered source factor, if this pure model handles it. -/
def pattern? : SourceKind → Option Atom
  | SourceKind.pathPattern pattern => some pattern
  | SourceKind.btm pattern => some pattern
  | _ => none

end SourceKind

namespace TemplateEffect

/-- The atom affected by an add/remove effect. -/
def payload? : TemplateEffect → Option Atom
  | TemplateEffect.add term => some term
  | TemplateEffect.remove term => some term
  | TemplateEffect.act _ term => some term
  | TemplateEffect.other _ => none

/-- Instantiate an effect under a query row and convert it to a reference-space mutation. -/
def toSpaceOp? (row : Bindings) : TemplateEffect → Option SpaceOp
  | TemplateEffect.add term => some (SpaceOp.add (instantiate row term))
  | TemplateEffect.remove term => some (SpaceOp.remove (instantiate row term))
  | TemplateEffect.act _ _ => none
  | TemplateEffect.other _ => none

end TemplateEffect

/-- True when an atom contains at least one variable occurrence. -/
def containsVars (atom : Atom) : Bool :=
  atom.vars != []

/-- True when a template payload is itself an `exec` atom. -/
def isExecTerm : Atom → Bool
  | Atom.expr (Atom.sym "exec" :: _) => true
  | _ => false

/-- Lower one source factor with its list index. -/
def lowerSource (index : Nat) (term : Atom) : LoweredSource :=
  { index, term, kind := sourceKind term }

/-- Lower all source factors, preserving source-list order. -/
def lowerSourcesFrom : Nat → List Atom → List LoweredSource
  | _, [] => []
  | index, term :: rest => lowerSource index term :: lowerSourcesFrom (index + 1) rest

/-- Lower all source factors from index zero. -/
def lowerSources (terms : List Atom) : List LoweredSource :=
  lowerSourcesFrom 0 terms

/-- Lower one template term with the metadata used by the planner. -/
def lowerEffect (mode : ListMode) (index : Nat) (term : Atom) : LoweredEffect :=
  let kind := templateKind mode term
  let payload := kind.payload?
  { index
    term
    kind
    bindingSensitive := payload.any containsVars
    addsExec := match kind with | TemplateEffect.add payload => isExecTerm payload | _ => false
    laterStepOutput := match kind with | TemplateEffect.add _ => true | _ => false }

/-- Lower all template terms, preserving template-list order. -/
def lowerEffectsFrom (mode : ListMode) : Nat → List Atom → List LoweredEffect
  | _, [] => []
  | index, term :: rest => lowerEffect mode index term :: lowerEffectsFrom mode (index + 1) rest

/-- Lower all template terms from index zero. -/
def lowerEffects (mode : ListMode) (terms : List Atom) : List LoweredEffect :=
  lowerEffectsFrom mode 0 terms

/-- Count whether a lowered source is an equation source. -/
def LoweredSource.isEquation (source : LoweredSource) : Bool :=
  match source.kind with
  | SourceKind.equation _ _ => true
  | _ => false

/-- Count whether a lowered source contributes a path-like reference query pattern. -/
def LoweredSource.isPathLike (source : LoweredSource) : Bool :=
  source.kind.pattern?.isSome

/-- Count whether a lowered effect is an add effect. -/
def LoweredEffect.isAdd (effect : LoweredEffect) : Bool :=
  match effect.kind with
  | TemplateEffect.add _ => true
  | _ => false

/-- Count whether a lowered effect is a remove effect. -/
def LoweredEffect.isRemove (effect : LoweredEffect) : Bool :=
  match effect.kind with
  | TemplateEffect.remove _ => true
  | _ => false

/-- Count whether a lowered effect is an ACT sink effect. -/
def LoweredEffect.isAct (effect : LoweredEffect) : Bool :=
  match effect.kind with
  | TemplateEffect.act _ _ => true
  | _ => false

/-- Build summary counters from the lowered factors and effects. -/
def summarize (sources : List LoweredSource) (effects : List LoweredEffect) : ExecSummary :=
  { sources := sources.length
    equationSources := (sources.filter LoweredSource.isEquation).length
    pathSources := (sources.filter LoweredSource.isPathLike).length
    addEffects := (effects.filter LoweredEffect.isAdd).length
    removeEffects := (effects.filter LoweredEffect.isRemove).length
    actEffects := (effects.filter LoweredEffect.isAct).length
    bindingSensitiveEffects := (effects.filter (fun effect => effect.bindingSensitive)).length
    bindingInsensitiveEffects := (effects.filter (fun effect => !(effect.bindingSensitive))).length
    addedExecs := (effects.filter (fun effect => effect.addsExec)).length
    laterStepOutputs := (effects.filter (fun effect => effect.laterStepOutput)).length }

/-- Lower a syntactic `(exec location sources templates)` atom into a pure plan. -/
def lowerExec? : Atom → Option ExecPlan
  | root@(Atom.expr [Atom.sym "exec", location, sourceList, templateList]) => do
      let (sourceMode, sourceTerms) ← sourceTerms? sourceList
      let (templateMode, templateTerms) ← templateTerms? templateList
      let sources := lowerSources sourceTerms
      let effects := lowerEffects templateMode templateTerms
      some
        { root
          location
          sourceMode
          templateMode
          sources
          effects
          summary := summarize sources effects }
  | _ => none

namespace LoweredSource

/-- The reference-space query pattern contributed by this source factor, if any. -/
def pattern? (source : LoweredSource) : Option Atom :=
  source.kind.pattern?

end LoweredSource

namespace ExecPlan

/-- Path-like source patterns handled by the reference-space evaluator. -/
def patterns (plan : ExecPlan) : List Atom :=
  plan.sources.filterMap LoweredSource.pattern?

/-- Add-effect payloads, useful when comparing to the older semantic `ExecRule` view. -/
def addTemplates (plan : ExecPlan) : List Atom :=
  plan.effects.filterMap (fun effect =>
    match effect.kind with
    | TemplateEffect.add term => some term
    | _ => none)

end ExecPlan

namespace SpaceOp

/-- Apply one reference-space mutation. -/
def apply : Space → SpaceOp → Space
  | space, SpaceOp.add atom => space.insert atom
  | space, SpaceOp.remove atom => space.removeOne atom

end SpaceOp

/-- Extend one seed row with one path-like query pattern. -/
def evalPathSource (space : Space) (row : Bindings) (pattern : Atom) : List Bindings :=
  (space.query (instantiate row pattern)).flatMap (fun queryRow => Bindings.merge row queryRow)

/-- Extend one seed row with one equality constraint. -/
def evalEquationSource (row : Bindings) (lhs rhs : Atom) : List Bindings :=
  (matchAtoms (instantiate row lhs) (instantiate row rhs)).flatMap (fun eqRow =>
    Bindings.merge row eqRow)

/-- Keep one seed row exactly when the two instantiated sides cannot match. -/
def evalInequalitySource (row : Bindings) (lhs rhs : Atom) : List Bindings :=
  if (matchAtoms (instantiate row lhs) (instantiate row rhs)).isEmpty then [row] else []

/-- Evaluate one lowered source factor against the reference `Space`.
ACT sources need a named resource store, so the plain evaluator leaves them empty. -/
def evalSource (space : Space) (row : Bindings) (source : LoweredSource) : List Bindings :=
  match source.kind with
  | SourceKind.pathPattern pattern => evalPathSource space row pattern
  | SourceKind.btm pattern => evalPathSource space row pattern
  | SourceKind.act _ _ => []
  | SourceKind.equation lhs rhs => evalEquationSource row lhs rhs
  | SourceKind.inequality lhs rhs => evalInequalitySource row lhs rhs
  | SourceKind.other _ => []

/-- Evaluate lowered source factors in source-list order. -/
def evalSources (space : Space) (sources : List LoweredSource) : List Bindings :=
  sources.foldl
    (fun rows source => rows.flatMap (fun row => evalSource space row source))
    [Bindings.empty]

/-- Apply one lowered effect under one query row. -/
def applyEffect (row : Bindings) (space : Space) (effect : LoweredEffect) : Space :=
  match effect.kind.toSpaceOp? row with
  | some op => SpaceOp.apply space op
  | none => space

/-- Apply all lowered effects under one query row. -/
def applyEffectsForRow (row : Bindings) (effects : List LoweredEffect) (space : Space) : Space :=
  effects.foldl (fun current effect => applyEffect row current effect) space

/-- Evaluate a plan over the reference `Space` and apply add/remove effects. -/
def applyPlan (space : Space) (plan : ExecPlan) : Space :=
  let rows := evalSources space plan.sources
  rows.foldl (fun current row => applyEffectsForRow row plan.effects current) space

/-- Claim the pending semantic exec rule with the lowest location. Ties keep the earlier rule. -/
def takeLowest : List MorkMM2.ExecRule → Option (MorkMM2.ExecRule × List MorkMM2.ExecRule)
  | [] => none
  | rule :: rest =>
      match takeLowest rest with
      | none => some (rule, [])
      | some (best, withoutBest) =>
          if rule.loc <= best.loc then
            some (rule, best :: withoutBest)
          else
            some (best, rule :: withoutBest)

/-- Consume and fire the lowest-location semantic exec rule, if one exists. -/
def stepByPriority : MorkMM2.ExecState → MorkMM2.ExecState
  | ⟨space, execs⟩ =>
      match takeLowest execs with
      | none => ⟨space, []⟩
      | some (rule, rest) => ⟨MorkMM2.insertProduced space (MorkMM2.producedAtoms space rule), rest⟩

/-- Run at most `fuel` priority-ordered MM2 exec steps. -/
def runByPriority : Nat → MorkMM2.ExecState → MorkMM2.ExecState
  | 0, state => state
  | n + 1, state => runByPriority n (stepByPriority state)

end MorkMM2Lowering

end Metta
