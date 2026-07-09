-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.MorkMM2Resources
Layer: Proofs
Purpose: Checked laws for the resource-aware MORK MM2 lowering layer. ACT sinks write instantiated
  payloads to named resources, ACT sources read those resources, and named ACT resources stay isolated
  from each other and from the main reference `Space`.
Imports: MettaHyperonFull.Proofs.MorkMM2Lowering, MettaHyperonFull.Core.MorkMM2Resources
Trusted boundary: none
Main exports: MorkMM2Resources.actName?_symbol, MorkMM2Resources.ResourceStore.queryAct_insert_same,
  MorkMM2Resources.ResourceStore.queryAct_insert_other,
  MorkMM2Resources.lowerEffect_output_act,
  MorkMM2Resources.applyEffectWithResources_act
Open obligations: host mmap/file behavior, external solver/native resources, resource locking, and
  resource failure reporting remain outside this pure proof layer.
-/
import MettaHyperonFull.Proofs.MorkMM2Lowering
import MettaHyperonFull.Core.MorkMM2Resources

namespace Metta

namespace MorkMM2Resources

open MorkMM2Lowering

/-- Symbol atoms are accepted as proof-facing ACT resource names. -/
theorem actName?_symbol (name : String) :
    actName? (Atom.sym name) = some name := rfl

/-- Grounded string atoms are accepted as proof-facing ACT resource names. -/
theorem actName?_groundedString (name : String) :
    actName? (Atom.gnd (Ground.str name)) = some name := rfl

namespace ResourceStore

/-- Querying the same ACT name after an insert sees the updated resource space. -/
theorem queryAct_insert_same (store : ResourceStore) (name : String) (atom pattern : Atom) :
    (store.insertAct name atom).queryAct name pattern =
      ((store.actSpace name).insert atom).query pattern := by
  simp [queryAct, insertAct]

/-- Inserting into one ACT name does not change a different ACT resource. -/
theorem queryAct_insert_other {store : ResourceStore} {name other : String} {atom pattern : Atom}
    (h : other ≠ name) :
    (store.insertAct name atom).queryAct other pattern =
      store.queryAct other pattern := by
  simp [queryAct, insertAct, h]

end ResourceStore

/-- `O` entries of the form `(ACT name term)` lower to ACT sink effects. -/
theorem lowerEffect_output_act (index : Nat) (name term : Atom) :
    lowerEffect ListMode.outputList index (Atom.expr [Atom.sym "ACT", name, term]) =
      { index := index
        term := Atom.expr [Atom.sym "ACT", name, term]
        kind := TemplateEffect.act name term
        bindingSensitive := containsVars term
        addsExec := false
        laterStepOutput := false } := rfl

/-- Applying an ACT effect writes the instantiated payload to the named resource. -/
theorem applyEffectWithResources_act (row : Bindings) (state : ExecResourceState)
    (index : Nat) (original payload : Atom) (bindingSensitive addsExec laterStepOutput : Bool)
    (name : String) :
    applyEffectWithResources row state
        { index := index
          term := original
          kind := TemplateEffect.act (Atom.sym name) payload
          bindingSensitive := bindingSensitive
          addsExec := addsExec
          laterStepOutput := laterStepOutput } =
      { state with resources := state.resources.insertAct name (instantiate row payload) } := rfl

/-- ACT sources refine rows by querying the named resource store. -/
theorem evalSourceWithResources_act (resources : ResourceStore) (space : Space)
    (row : Bindings) (index : Nat) (original name pattern : Atom) :
    evalSourceWithResources resources space row
        { index := index
          term := original
          kind := SourceKind.act name pattern } =
      evalActSource resources row name pattern := rfl

private def msg (tag : String) : Atom :=
  Atom.expr [Atom.sym "Msg", Atom.sym tag]

private def seen (tag : String) : Atom :=
  Atom.expr [Atom.sym "Seen", Atom.sym tag]

private def actWriteEffect : LoweredEffect :=
  lowerEffect ListMode.outputList 0
    (Atom.expr [Atom.sym "ACT", Atom.sym "memo", msg "X"])

private def actWritePlan : ExecPlan :=
  { root := Atom.sym "fixture"
    location := Atom.sym "write-act"
    sourceMode := ListMode.sourceList
    templateMode := ListMode.outputList
    sources := []
    effects := [actWriteEffect]
    summary := summarize [] [actWriteEffect] }

private def actReadSource : LoweredSource :=
  { index := 0
    term := Atom.expr [Atom.sym "ACT", Atom.sym "memo", Atom.expr [Atom.sym "Msg", Atom.var "x"]]
    kind := SourceKind.act (Atom.sym "memo") (Atom.expr [Atom.sym "Msg", Atom.var "x"]) }

private def actReadEffect : LoweredEffect :=
  lowerEffect ListMode.outputList 0
    (Atom.expr [Atom.sym "+", Atom.expr [Atom.sym "Seen", Atom.var "x"]])

private def actReadPlan : ExecPlan :=
  { root := Atom.sym "fixture"
    location := Atom.sym "read-act"
    sourceMode := ListMode.sourceList
    templateMode := ListMode.outputList
    sources := [actReadSource]
    effects := [actReadEffect]
    summary := summarize [actReadSource] [actReadEffect] }

private def afterActWrite : ExecResourceState :=
  applyPlanWithResources ExecResourceState.empty actWritePlan

/-- ACT sink effects do not insert their payload into the main reference space. -/
example :
    afterActWrite.space.contains (msg "X") = false := rfl

/-- ACT sink effects do not leak into other ACT names. -/
example :
    afterActWrite.resources.queryAct "other" (msg "X") = [] := rfl

/-- Lowering records ACT sink effects in the executable summary. -/
example :
    actWritePlan.summary.actEffects = 1 := rfl

end MorkMM2Resources

end Metta
