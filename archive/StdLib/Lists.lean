import MettaHyperonFull.StdLib.Atoms

namespace Metta.StdLib
open Metta

def mapAtom (xs : List Atom) (f : Atom → Atom) : Atom := Atom.expr (xs.map f)
def filterAtom (xs : List Atom) (p : Atom → Bool) : Atom := Atom.expr (xs.filter p)
def foldlAtom (xs : List Atom) (init : Atom) (f : Atom → Atom → Atom) : Atom := xs.foldl f init

def formatArgs (xs : List Atom) : Atom := Atom.expr xs

end Metta.StdLib
