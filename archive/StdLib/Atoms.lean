import MettaHyperonFull.Core.Builtins

namespace Metta.StdLib
open Metta

def consAtom (h t : Atom) : Atom := match t with | Atom.expr xs => Atom.expr (h::xs) | _ => Atom.expr [h,t]
def deconsAtom : Atom → Atom
  | Atom.expr (h::t) => Atom.expr [h, Atom.expr t]
  | _ => Atom.empty

def carAtom : Atom → Atom
  | Atom.expr (h::_) => h
  | _ => Atom.empty

def cdrAtom : Atom → Atom
  | Atom.expr (_::t) => Atom.expr t
  | _ => Atom.empty

def sizeAtom (a : Atom) : Atom := Atom.gnd (Ground.int (Int.ofNat (Atom.size a)))
def indexAtom : Atom → Nat → Atom
  | Atom.expr xs, n => xs.getD n Atom.empty
  | _, _ => Atom.empty

end Metta.StdLib
