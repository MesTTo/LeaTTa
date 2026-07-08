-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

import MettaHyperonFull.Operational.Minimal

namespace Metta.StdLib
open Metta

def ifAtom (cond th el : Atom) : Atom :=
  match cond with
  | Atom.gnd (Ground.bool true) => th
  | Atom.sym "True" => th
  | Atom.gnd (Ground.bool false) => el
  | Atom.sym "False" => el
  | _ => Atom.expr [Atom.sym "if", cond, th, el]

def letAtom (x : VarName) (v body : Atom) : Atom := Subst.apply [(x,v)] body

def letStar (bindings : List (VarName × Atom)) (body : Atom) : Atom := Subst.apply bindings body

def switchAtom (a : Atom) (cases : List (Atom × Atom)) : List Atom :=
  cases.filterMap (fun p => match matchAtoms a p.fst with | b :: _ => some (instantiate b p.snd) | [] => none)

end Metta.StdLib
