import MettaHyperonFull.Core.Atom

namespace Metta

/-- The four evaluation outcomes from the Hyperon spec: an ordinary value, `Empty` (prune branch),
    `NotReducible` (no rule applied), or an `Error`. The nondeterministic result list and binding
    pairing are handled in later modules. -/
inductive EvalStatus where
  | value : Atom → EvalStatus
  | empty : EvalStatus
  | notReducible : Atom → EvalStatus
  | error : Atom → String → EvalStatus
  deriving Repr, BEq, Inhabited

/-- Reify an `EvalStatus` back into the atom that represents it: a value as itself, `empty` as the
    `Empty` symbol, `notReducible` as its atom, and `error` as `(Error a "msg")`. -/
def EvalStatus.toAtom : EvalStatus → Atom
  | EvalStatus.value a => a
  | EvalStatus.empty => Atom.empty
  | EvalStatus.notReducible a => a
  | EvalStatus.error a msg => Atom.expr [Atom.sym "Error", a, Atom.gnd (Ground.str msg)]

end Metta
