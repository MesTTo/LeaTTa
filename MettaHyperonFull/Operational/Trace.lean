import MettaHyperonFull.Operational.Semantics

namespace Metta

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

def traceRunFuel (cfg : RuntimeConfig) : Nat → State → Trace
  | 0, s => Trace.empty s
  | Nat.succ n, s =>
      match smallStep? cfg s with
      | none => Trace.empty s
      | some (k, s') => Trace.extend (traceRunFuel cfg n s') k s'

end Metta
