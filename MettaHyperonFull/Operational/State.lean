import MettaHyperonFull.Core.Space
import MettaHyperonFull.Core.Grounding
import MettaHyperonFull.Core.Builtins

namespace Metta

/-- The four-register MeTTa machine state from arXiv:2305.17218 §3: input `i`, knowledge base `k`,
    workspace `w`, and output `o`. The `history` field records the sequence of step labels, used for
    trace collection and bisimulation proofs. -/
structure State where
  input : Space
  kb : Space
  work : Space
  output : Space
  history : List Atom := []
  deriving Repr, BEq, Inhabited

namespace State

def empty : State := ⟨Space.empty, Space.empty, Space.empty, Space.empty, []⟩
def withInput (xs : List Atom) : State := { empty with input := ⟨xs⟩ }
def pushInput (s : State) (a : Atom) : State := { s with input := Space.insert s.input a }
/-- Append `a` to the back of the input register. Use this (not `pushInput`) when program order
    (FIFO) must be preserved. -/
def enqueueInput (s : State) (a : Atom) : State := { s with input := ⟨s.input.atoms ++ [a]⟩ }
def pushWork (s : State) (a : Atom) : State := { s with work := Space.insert s.work a }
def pushOutput (s : State) (a : Atom) : State := { s with output := Space.insert s.output a }
def addKb (s : State) (a : Atom) : State := { s with kb := Space.insert s.kb a }
def remKb (s : State) (a : Atom) : State := { s with kb := Space.removeOne s.kb a }
def trace (s : State) (label : String) (payload : Atom) : State :=
  { s with history := Atom.expr [Atom.sym label, payload] :: s.history }

end State

/-- A resource token for the gas extension of Meta-MeTTa (arXiv:2305.17218 §6). `energy` is the
    remaining gas budget; `principalHash` identifies the payer. -/
structure ResourceToken where
  principalHash : String
  energy : Int
  deriving Repr, BEq, Inhabited

structure RuntimeConfig where
  fuel : Nat := 256
  groundings : GroundingTable := Builtins.table
  deriving Inhabited

end Metta
