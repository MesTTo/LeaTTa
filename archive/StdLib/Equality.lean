import MettaHyperonFull.Core.Space
import MettaHyperonFull.Core.Alpha

namespace Metta.StdLib
open Metta

/-- Reduction rule definition `(= lhs rhs)`. -/
def reduct (lhs rhs : Atom) : Atom := Atom.expr [Atom.sym "=", lhs, rhs]
def id (a : Atom) : Atom := a
def alphaEqual (a b : Atom) : Atom := Atom.gnd (Ground.bool (alphaEq a b))
def ifEqual (a b th el : Atom) : Atom := if a == b then th else el

def noreduceEq (lhs rhs : Atom) : Atom := Atom.expr [Atom.sym "noreduce-eq", lhs, rhs]

end Metta.StdLib
