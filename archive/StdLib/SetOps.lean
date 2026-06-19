import MettaHyperonFull.Core.Atom

namespace Metta.StdLib
open Metta

def uniqueList : List Atom → List Atom
  | [] => []
  | x :: rest => if rest.any (fun y => y == x) then uniqueList rest else x :: uniqueList rest

def unionAtom (a b : Atom) : Atom :=
  match a, b with
  | Atom.expr xs, Atom.expr ys => Atom.expr (uniqueList (xs ++ ys))
  | _, _ => Atom.empty

def intersectionAtom (a b : Atom) : Atom :=
  match a, b with
  | Atom.expr xs, Atom.expr ys => Atom.expr (uniqueList (xs.filter (fun x => ys.any (fun y => y == x))))
  | _, _ => Atom.empty

def subtractionAtom (a b : Atom) : Atom :=
  match a, b with
  | Atom.expr xs, Atom.expr ys => Atom.expr (xs.filter (fun x => !(ys.any (fun y => y == x))))
  | _, _ => Atom.empty

end Metta.StdLib
