-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Minimal.Observation
Layer: Minimal
Purpose: Theorem-facing observation bridge for one top-level directive. It records the input query,
  fuel budget, result atoms, error atoms, stack-overflow flag, and before/after world state produced
  by the existing minimal evaluator. This is a named boundary over current runtime behavior, not a
  new evaluator.
Imports: MettaHyperonFull.Minimal.Stdlib
Trusted boundary: none
Main exports: WorldDelta, DirectiveObservation, observedEnv, observeQuery,
  observeQuery_results, observeQuery_errors, observeQuery_worldBefore, observeQuery_worldAfter
Open obligations: richer trace-sensitive observations can extend this record when a theorem needs
  step-by-step evidence.
-/
import MettaHyperonFull.Minimal.Stdlib

namespace Metta.Minimal
open Metta

/-- The world before and after one observed directive. -/
structure WorldDelta where
  before : World
  after : World

/-- True for the stack-overflow error shape emitted by the minimal evaluator. -/
def isStackOverflowAtom : Atom -> Bool
  | Atom.expr [Atom.sym "Error", _, Atom.sym "StackOverflow"] => true
  | _ => false

/-- A theorem-facing observation for one directive. -/
structure DirectiveObservation where
  input : Atom
  fuel : Nat
  results : List Atom
  errors : List Atom
  exhausted : Bool
  worldDelta : WorldDelta

open Std in
/-- Build the evaluation environment used by observed top-level directives. -/
def observedEnv (kbAtoms : List Atom)
    (imports : HashMap String (List Atom) := HashMap.emptyWithCapacity)
    (importDeps : HashMap String (List String) := HashMap.emptyWithCapacity) : MinEnv :=
  { MinEnv.ofAtomsGT (preludeAtoms ++ kbAtoms) stdGroundings with
    imports := imports, importDeps := importDeps, visibleAtoms := kbAtoms }

open Std in
/-- Observe one query under the current knowledge base and threaded state. -/
def observeQuery (kbAtoms : List Atom) (fuel : Nat) (st : St) (q : Atom)
    (imports : HashMap String (List Atom) := HashMap.emptyWithCapacity)
    (importDeps : HashMap String (List String) := HashMap.emptyWithCapacity) :
    DirectiveObservation :=
  let env := observedEnv kbAtoms imports importDeps
  let (pairs, st') := mettaEval env fuel st [] q
  let results := pairs.map (·.1)
  { input := q,
    fuel := fuel,
    results := results,
    errors := results.filter Atom.isError,
    exhausted := results.any isStackOverflowAtom,
    worldDelta := { before := st.world, after := st'.world } }

open Std in
theorem observeQuery_results (kbAtoms : List Atom) (fuel : Nat) (st : St) (q : Atom)
    (imports : HashMap String (List Atom) := HashMap.emptyWithCapacity)
    (importDeps : HashMap String (List String) := HashMap.emptyWithCapacity) :
    (observeQuery kbAtoms fuel st q imports importDeps).results =
      (mettaEval (observedEnv kbAtoms imports importDeps) fuel st [] q).1.map (·.1) := by
  simp [observeQuery]

open Std in
theorem observeQuery_errors (kbAtoms : List Atom) (fuel : Nat) (st : St) (q : Atom)
    (imports : HashMap String (List Atom) := HashMap.emptyWithCapacity)
    (importDeps : HashMap String (List String) := HashMap.emptyWithCapacity) :
    (observeQuery kbAtoms fuel st q imports importDeps).errors =
      (observeQuery kbAtoms fuel st q imports importDeps).results.filter Atom.isError := by
  simp [observeQuery]

open Std in
theorem observeQuery_worldBefore (kbAtoms : List Atom) (fuel : Nat) (st : St) (q : Atom)
    (imports : HashMap String (List Atom) := HashMap.emptyWithCapacity)
    (importDeps : HashMap String (List String) := HashMap.emptyWithCapacity) :
    (observeQuery kbAtoms fuel st q imports importDeps).worldDelta.before = st.world := by
  simp [observeQuery]

open Std in
theorem observeQuery_worldAfter (kbAtoms : List Atom) (fuel : Nat) (st : St) (q : Atom)
    (imports : HashMap String (List Atom) := HashMap.emptyWithCapacity)
    (importDeps : HashMap String (List String) := HashMap.emptyWithCapacity) :
    (observeQuery kbAtoms fuel st q imports importDeps).worldDelta.after =
      (mettaEval (observedEnv kbAtoms imports importDeps) fuel st [] q).2.world := by
  simp [observeQuery]

end Metta.Minimal
