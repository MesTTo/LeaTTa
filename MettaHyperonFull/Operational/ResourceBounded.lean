import MettaHyperonFull.Operational.Semantics

namespace Metta

/-- A concrete syntactic cost model for Meta-MeTTa's abstract cost function `#` (MOPS §6). The cost
    of consuming an atom is its size (`Atom.size`). Any non-negative cost preserves the gas invariant
    `resourceStep?_energy_nonincreasing`; atom size is the natural syntactic measure here. -/
def transitionCost (a : Atom) : Int := Int.ofNat (Atom.size a)

def affordable (tok : ResourceToken) (a : Atom) : Bool := tok.energy - transitionCost a > 0

def debit (tok : ResourceToken) (a : Atom) : ResourceToken := { tok with energy := tok.energy - transitionCost a }

structure ResourceState where
  state : State
  tokens : List ResourceToken
  deriving Repr, BEq, Inhabited

/-- One resource-guarded step. Consumes the head input atom and debits the head token, but only if
    the token can afford the atom's syntactic cost. Returns `none` if input is empty, there are no
    tokens, or the head token cannot afford the head atom. -/
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
