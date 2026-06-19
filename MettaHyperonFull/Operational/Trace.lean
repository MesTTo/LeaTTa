import MettaHyperonFull.Operational.Semantics

namespace Metta

/-- A recorded execution: the sequence of states visited and the step label that caused each
    transition. `states` has one more element than `labels`. -/
structure Trace where
  states : List State
  labels : List StepKind
  deriving Repr, Inhabited

namespace Trace

/-- Start a trace at the initial state `s` (no steps taken yet). -/
def empty (s : State) : Trace := ⟨[s], []⟩
/-- Append one transition `k → s` to a trace. -/
def extend (tr : Trace) (k : StepKind) (s : State) : Trace :=
  { states := tr.states ++ [s], labels := tr.labels ++ [k] }

/-- The output register at each state in the trace, in order. -/
def observations (tr : Trace) : List Space := tr.states.map (fun s => s.output)

end Trace

/-- Run the machine for up to `n` steps, recording every transition. Stops early if `smallStep?`
    returns `none`. -/
def traceRunFuel (cfg : RuntimeConfig) : Nat → State → Trace
  | 0, s => Trace.empty s
  | Nat.succ n, s =>
      match smallStep? cfg s with
      | none => Trace.empty s
      | some (k, s') => Trace.extend (traceRunFuel cfg n s') k s'

end Metta
