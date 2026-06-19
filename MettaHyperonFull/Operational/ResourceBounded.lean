import MettaHyperonFull.Operational.Semantics

namespace Metta

/-- A concrete syntactic cost model instantiating Meta-MeTTa's abstract cost function `#` (MOPS §6):
the cost of consuming an atom is its size. Any non-negative cost makes the gas invariant
(`Operational/Properties.lean : resourceStep?_energy_nonincreasing`) hold; atom size is the canonical
syntactic measure. -/
def transitionCost (a : Atom) : Int := Int.ofNat (Atom.size a)

def affordable (tok : ResourceToken) (a : Atom) : Bool := tok.energy - transitionCost a > 0

def debit (tok : ResourceToken) (a : Atom) : ResourceToken := { tok with energy := tok.energy - transitionCost a }

structure ResourceState where
  state : State
  tokens : List ResourceToken
  deriving Repr, BEq, Inhabited

/-- A resource guarded step: refuse to consume an input if no token can pay its syntactic cost. -/
def resourceStep? (cfg : RuntimeConfig) (rs : ResourceState) : Option ResourceState :=
  match rs.state.input.atoms, rs.tokens with
  | [], _ => none
  | _, [] => none
  | a :: _, t :: ts =>
      if affordable t a then
        match smallStep? cfg rs.state with
        | some (_, st') => some { rs with state := st', tokens := debit t a :: ts }
        | none => none
      else none

end Metta
