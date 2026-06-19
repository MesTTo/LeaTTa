import MettaHyperonFull.Core.Atom

namespace Metta

/-- Nondeterministic result list paired with variable bindings is modelled in later modules.
    This type captures the three special result classes in the Hyperon spec: ordinary results,
    Empty, NotReducible, and Error. -/
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
