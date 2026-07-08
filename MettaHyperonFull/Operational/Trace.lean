-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Operational.Trace
Layer: Operational
Purpose: Execution traces of the four-register machine, the observable history of a run. A `Trace`
  records the sequence of states visited and the step label that caused each transition.
  `traceRunFuel` runs the machine for up to `n` steps while recording every transition, and
  `observations` projects out the output register at each state.
Imports: MettaHyperonFull.Operational.Semantics
Trusted boundary: none
Main exports: Trace, Trace.empty, Trace.extend, Trace.observations, traceRunFuel
Open obligations: none
-/
import MettaHyperonFull.Operational.Semantics

namespace Metta

/-- A recorded execution: the sequence of states visited and the step label that caused each
    transition. `states` has one more element than `labels`. -/
structure Trace where
  states : List State
  labels : List StepKind
  deriving Repr, Inhabited

namespace Trace

def empty (s : State) : Trace := ⟨[s], []⟩
def extend (tr : Trace) (k : StepKind) (s : State) : Trace :=
  { states := tr.states ++ [s], labels := tr.labels ++ [k] }

def observations (tr : Trace) : List Space := tr.states.map (fun s => s.output)

end Trace

/-- Run the machine for up to `n` steps, recording every transition. Stops early if `smallStep?`
    returns `none`. -/
def traceRunFuel (cfg : RuntimeConfig) : Nat → State → Trace
  | 0, s => Trace.empty s
  | Nat.succ n, s =>
      match smallStep? cfg s with
      | none => Trace.empty s
      | some (k, s') =>
          -- Record `s` (the pre-step state) and the label `k`, then the trace from `s'`.
          -- The recursive trace already starts at `s'`, so we prepend `s`/`k` to it.
          let rest := traceRunFuel cfg n s'
          { states := s :: rest.states, labels := k :: rest.labels }

end Metta
