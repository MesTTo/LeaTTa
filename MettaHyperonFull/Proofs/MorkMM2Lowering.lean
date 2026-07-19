-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.MorkMM2Lowering
Layer: Proofs
Purpose: Checked laws for the MORK MM2 lowering view: `I` and `O` list recognition, comma-template
  compatibility with the older semantic add-only rule view, equality and inequality source evaluation,
  add/remove effect application, and lowest-location priority selection.
Imports: MettaHyperonFull.Proofs.MorkMM2, MettaHyperonFull.Core.MorkMM2Lowering
Trusted boundary: none
Main exports: MorkMM2Lowering.sourceTerms?_I, MorkMM2Lowering.templateTerms?_O,
  MorkMM2Lowering.lowerEffect_conjunction_add, MorkMM2Lowering.lowerEffect_output_add,
  MorkMM2Lowering.lowerEffect_output_remove, MorkMM2Lowering.applyEffect_add,
  MorkMM2Lowering.applyEffect_remove, MorkMM2Lowering.evalSource_equation,
  MorkMM2Lowering.takeLowest_single
Open obligations: external source and sink resources remain outside this module.
-/
import MettaHyperonFull.Proofs.MorkMM2
import MettaHyperonFull.Core.MorkMM2Lowering

namespace Metta

namespace MorkMM2Lowering

/-- Source lists headed by `I` are recognized as MM2 source lists. -/
theorem sourceTerms?_I (a b : Atom) :
    sourceTerms? (Atom.expr [Atom.sym "I", a, b]) =
      some (ListMode.sourceList, [a, b]) := rfl

/-- Template lists headed by `O` are recognized as MM2 output/effect lists. -/
theorem templateTerms?_O (a b : Atom) :
    templateTerms? (Atom.expr [Atom.sym "O", a, b]) =
      some (ListMode.outputList, [a, b]) := rfl

/-- Ordinary comma template entries lower to add effects, matching the first semantic MM2 model. -/
theorem lowerEffect_conjunction_add (index : Nat) (term : Atom) :
    lowerEffect ListMode.conjunction index term =
      { index := index
        term := term
        kind := TemplateEffect.add term
        bindingSensitive := containsVars term
        addsExec := isExecTerm term
        laterStepOutput := true } := rfl

/-- `O` entries of the form `(+ term)` lower to add effects. -/
theorem lowerEffect_output_add (index : Nat) (term : Atom) :
    lowerEffect ListMode.outputList index (Atom.expr [Atom.sym "+", term]) =
      { index := index
        term := Atom.expr [Atom.sym "+", term]
        kind := TemplateEffect.add term
        bindingSensitive := containsVars term
        addsExec := isExecTerm term
        laterStepOutput := true } := rfl

/-- `O` entries of the form `(- term)` lower to remove-one effects. -/
theorem lowerEffect_output_remove (index : Nat) (term : Atom) :
    lowerEffect ListMode.outputList index (Atom.expr [Atom.sym "-", term]) =
      { index := index
        term := Atom.expr [Atom.sym "-", term]
        kind := TemplateEffect.remove term
        bindingSensitive := containsVars term
        addsExec := false
        laterStepOutput := false } := rfl

/-- Equality sources refine the current row by matching the instantiated sides. -/
theorem evalSource_equation (space : Space) (row : Bindings) (index : Nat)
    (original lhs rhs : Atom) :
    evalSource space row
        { index := index
          term := original
          kind := SourceKind.equation lhs rhs } =
      evalEquationSource row lhs rhs := rfl

/-- Inequality keeps a row when the instantiated sides cannot match. -/
theorem evalInequalitySource_different_symbols (row : Bindings) :
    evalInequalitySource row (Atom.sym "X") (Atom.sym "Y") = [row] := by
  simp [evalInequalitySource, instantiate, Bindings.resolveAtom, matchAtoms, matchAtomsWith]

/-- Inequality rejects a row when the instantiated sides already match. -/
theorem evalInequalitySource_same_symbol (row : Bindings) :
    evalInequalitySource row (Atom.sym "X") (Atom.sym "X") = [] := by
  simp [evalInequalitySource, instantiate, Bindings.resolveAtom, matchAtoms, matchAtomsWith]

/-- Applying an add effect inserts the instantiated payload into the reference space. -/
theorem applyEffect_add (row : Bindings) (space : Space) (index : Nat)
    (original payload : Atom) (bindingSensitive addsExec laterStepOutput : Bool) :
    applyEffect row space
        { index := index
          term := original
          kind := TemplateEffect.add payload
          bindingSensitive := bindingSensitive
          addsExec := addsExec
          laterStepOutput := laterStepOutput } =
      space.insert (instantiate row payload) := rfl

/-- Applying a remove effect removes one copy of the instantiated payload from the reference space. -/
theorem applyEffect_remove (row : Bindings) (space : Space) (index : Nat)
    (original payload : Atom) (bindingSensitive addsExec laterStepOutput : Bool) :
    applyEffect row space
        { index := index
          term := original
          kind := TemplateEffect.remove payload
          bindingSensitive := bindingSensitive
          addsExec := addsExec
          laterStepOutput := laterStepOutput } =
      space.removeOne (instantiate row payload) := rfl

/-- No pending semantic exec rules means no priority claim. -/
theorem takeLowest_nil :
    takeLowest [] = (none : Option (MorkMM2.ExecRule × List MorkMM2.ExecRule)) := rfl

/-- A single semantic exec rule is the priority claim and leaves no pending rules. -/
theorem takeLowest_single (rule : MorkMM2.ExecRule) :
    takeLowest [rule] = some (rule, []) := rfl

private def never (tag : String) : Atom :=
  Atom.expr [Atom.sym "Never", Atom.sym tag]

private def out (tag : String) : Atom :=
  Atom.expr [Atom.sym "Out", Atom.sym tag]

private def highRule : MorkMM2.ExecRule :=
  { loc := 1, patterns := [never "high"], templates := [out "high"] }

private def lowRule : MorkMM2.ExecRule :=
  { loc := 0, patterns := [never "low"], templates := [out "low"] }

private def eqSource : Atom :=
  Atom.expr [Atom.sym "==", Atom.expr [Atom.sym "Knowledge", Atom.var "value"], Atom.var "whole"]

private def outEffect : Atom :=
  Atom.expr [Atom.sym "+", Atom.expr [Atom.sym "query-result", Atom.var "whole"]]

private def val (tag : String) : Atom :=
  Atom.expr [Atom.sym "VAL", Atom.sym tag]

private def ioExec : Atom :=
  Atom.expr
    [ Atom.sym "exec",
      Atom.sym "formal-query",
      Atom.expr [Atom.sym "I", eqSource],
      Atom.expr [Atom.sym "O", outEffect] ]

private def valueSpace : Space :=
  ⟨[val "X", val "Y", val "Z"]⟩

private def valuePathSource : LoweredSource :=
  { index := 0
    term := Atom.expr [Atom.sym "VAL", Atom.var "x"]
    kind := SourceKind.pathPattern (Atom.expr [Atom.sym "VAL", Atom.var "x"]) }

private def wholeValueSource : LoweredSource :=
  { index := 1
    term := Atom.expr
      [ Atom.sym "==",
        Atom.expr [Atom.sym "VAL", Atom.var "x"],
        Atom.var "whole" ]
    kind := SourceKind.equation
      (Atom.expr [Atom.sym "VAL", Atom.var "x"])
      (Atom.var "whole") }

private def pairLeftSource : LoweredSource :=
  { index := 0
    term := Atom.expr [Atom.sym "VAL", Atom.var "x"]
    kind := SourceKind.pathPattern (Atom.expr [Atom.sym "VAL", Atom.var "x"]) }

private def pairRightSource : LoweredSource :=
  { index := 1
    term := Atom.expr [Atom.sym "VAL", Atom.var "y"]
    kind := SourceKind.pathPattern (Atom.expr [Atom.sym "VAL", Atom.var "y"]) }

private def pairDistinctSource : LoweredSource :=
  { index := 2
    term := Atom.expr
      [ Atom.sym "!=",
        Atom.expr [Atom.sym "VAL", Atom.var "x"],
        Atom.expr [Atom.sym "VAL", Atom.var "y"] ]
    kind := SourceKind.inequality
      (Atom.expr [Atom.sym "VAL", Atom.var "x"])
      (Atom.expr [Atom.sym "VAL", Atom.var "y"]) }

private def seenWholePlan : ExecPlan :=
  { root := Atom.sym "fixture"
    location := Atom.sym "eq"
    sourceMode := ListMode.sourceList
    templateMode := ListMode.outputList
    sources := [valuePathSource, wholeValueSource]
    effects :=
      [lowerEffect ListMode.outputList 0
        (Atom.expr [Atom.sym "+", Atom.expr [Atom.sym "Seen", Atom.var "whole"]])]
    summary := summarize [valuePathSource, wholeValueSource]
      [lowerEffect ListMode.outputList 0
        (Atom.expr [Atom.sym "+", Atom.expr [Atom.sym "Seen", Atom.var "whole"]])] }

private def distinctPairsPlan : ExecPlan :=
  { root := Atom.sym "fixture"
    location := Atom.sym "neq"
    sourceMode := ListMode.sourceList
    templateMode := ListMode.outputList
    sources := [pairLeftSource, pairRightSource, pairDistinctSource]
    effects :=
      [lowerEffect ListMode.outputList 0
        (Atom.expr
          [ Atom.sym "+",
            Atom.expr [Atom.sym "OUT", Atom.var "x", Atom.var "y"] ])]
    summary := summarize [pairLeftSource, pairRightSource, pairDistinctSource]
      [lowerEffect ListMode.outputList 0
        (Atom.expr
          [ Atom.sym "+",
            Atom.expr [Atom.sym "OUT", Atom.var "x", Atom.var "y"] ])] }

/-- The lowering fixture records `I` source mode, `O` template mode, equation source, and add effect. -/
example :
    (lowerExec? ioExec).map (fun plan =>
        ( plan.sourceMode,
          plan.templateMode,
          plan.summary.sources,
          plan.summary.equationSources,
          plan.summary.pathSources,
          plan.summary.addEffects,
          plan.summary.laterStepOutputs )) =
      some
        ( ListMode.sourceList,
          ListMode.outputList,
          1,
          1,
          0,
          1,
          1 ) := by
  rfl

/-- Priority claiming chooses the lower location even when it appears second in the pending list. -/
example :
    (takeLowest [highRule, lowRule]).map (fun pair =>
        (pair.fst.loc, pair.snd.map MorkMM2.ExecRule.loc)) =
      some (0, [1]) := by
  rfl

/-- A priority step consumes the lower-location rule first. -/
example :
    (stepByPriority { space := Space.empty, execs := [highRule, lowRule] }).execs.map
        MorkMM2.ExecRule.loc = [1] := by
  rfl

end MorkMM2Lowering

end Metta
