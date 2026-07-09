-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.MorkMM2Resources
Layer: Core
Purpose: Resource-aware execution for lowered MORK MM2 plans. ACT-backed sources and sinks are
  modeled as named spaces outside the main reference `Space`; non-ACT effects still update the main
  space. This captures the MORK resource boundary without modeling host file I/O.
Imports: MettaHyperonFull.Core.MorkMM2Lowering
Trusted boundary: none
Main exports: MorkMM2Resources.ResourceStore, MorkMM2Resources.ExecResourceState,
  MorkMM2Resources.evalSourceWithResources, MorkMM2Resources.applyPlanWithResources
Open obligations: concrete ACT mmap loading/dumping, resource locking, Z3/WASM/native resources, and
  resource error/cancellation behavior remain host-runtime refinements.
-/
import MettaHyperonFull.Core.MorkMM2Lowering

namespace Metta

namespace MorkMM2Resources

open MorkMM2Lowering

/-- Resource names accepted by the proof-facing ACT model. -/
def actName? : Atom → Option String
  | Atom.sym name => some name
  | Atom.gnd (Ground.str name) => some name
  | _ => none

/-- Named ACT resources as total map from file/resource name to a reference `Space`. -/
structure ResourceStore where
  actSpace : String → Space

namespace ResourceStore

/-- Empty resource store. Every ACT name starts as an empty space. -/
def empty : ResourceStore :=
  { actSpace := fun _ => Space.empty }

/-- Query a named ACT resource. -/
def queryAct (store : ResourceStore) (name : String) (pattern : Atom) : List Bindings :=
  (store.actSpace name).query pattern

/-- Add one atom to a named ACT resource, leaving every other ACT name unchanged. -/
def insertAct (store : ResourceStore) (name : String) (atom : Atom) : ResourceStore :=
  { actSpace := fun queryName =>
      if queryName == name then
        (store.actSpace queryName).insert atom
      else
        store.actSpace queryName }

end ResourceStore

/-- Main-space state paired with external resources used by lowered MM2 plans. -/
structure ExecResourceState where
  space : Space
  resources : ResourceStore

namespace ExecResourceState

/-- Empty main space and empty resources. -/
def empty : ExecResourceState :=
  { space := Space.empty, resources := ResourceStore.empty }

end ExecResourceState

/-- Extend one row by querying an ACT resource source. -/
def evalActSource (resources : ResourceStore) (row : Bindings) (name pattern : Atom) :
    List Bindings :=
  match actName? name with
  | some actName =>
      (resources.queryAct actName (instantiate row pattern)).flatMap (fun queryRow =>
        Bindings.merge row queryRow)
  | none => []

/-- Evaluate one lowered source factor against the main space and named resources. -/
def evalSourceWithResources (resources : ResourceStore) (space : Space) (row : Bindings)
    (source : LoweredSource) : List Bindings :=
  match source.kind with
  | SourceKind.act name pattern => evalActSource resources row name pattern
  | _ => evalSource space row source

/-- Evaluate lowered sources left-to-right with access to the main space and named resources. -/
def evalSourcesWithResources (resources : ResourceStore) (space : Space)
    (sources : List LoweredSource) : List Bindings :=
  sources.foldl
    (fun rows source => rows.flatMap (fun row => evalSourceWithResources resources space row source))
    [Bindings.empty]

/-- Apply one lowered effect under a row, writing ACT effects to the named resource store. -/
def applyEffectWithResources (row : Bindings) (state : ExecResourceState)
    (effect : LoweredEffect) : ExecResourceState :=
  match effect.kind with
  | TemplateEffect.add term =>
      { state with space := state.space.insert (instantiate row term) }
  | TemplateEffect.remove term =>
      { state with space := state.space.removeOne (instantiate row term) }
  | TemplateEffect.act name term =>
      match actName? name with
      | some actName =>
          { state with resources := state.resources.insertAct actName (instantiate row term) }
      | none => state
  | TemplateEffect.other _ => state

/-- Apply all lowered effects under one row. -/
def applyEffectsForRowWithResources (row : Bindings) (effects : List LoweredEffect)
    (state : ExecResourceState) : ExecResourceState :=
  effects.foldl (fun current effect => applyEffectWithResources row current effect) state

/-- Evaluate a lowered MM2 plan over the main space and named resources. -/
def applyPlanWithResources (state : ExecResourceState) (plan : ExecPlan) : ExecResourceState :=
  let rows := evalSourcesWithResources state.resources state.space plan.sources
  rows.foldl (fun current row => applyEffectsForRowWithResources row plan.effects current) state

end MorkMM2Resources

end Metta
