import MettaHyperonFull.Operational.Semantics

namespace Metta

/-- A self-modification is a state transition that changes its own knowledge base. -/
def modifiesOwnKB (s t : State) : Bool := !(s.kb == t.kb)

/-- Reflectively activate a subprogram by injecting it into the input register. -/
def activate (program : Atom) (s : State) : State := State.pushInput s program

/-- Record a trace as MeTTa atoms in a history space. -/
def traceAsAtoms (tr : List State) : List Atom :=
  tr.zipIdx.map (fun (st, i) => Atom.expr [Atom.sym "trace-state", Atom.gnd (Ground.int (Int.ofNat i)), Atom.expr st.output.atoms])

end Metta
