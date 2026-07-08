-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

import MettaHyperonFull.Operational.Minimal

namespace Metta.StdLib

open Metta

def superpose : Atom → List Atom
  | Atom.expr xs => xs
  | a => [a]

def collapse (xs : List Atom) : Atom := Atom.expr xs

def collapseBind (cfg : RuntimeConfig) (ctx : Space) (a : Atom) : Atom :=
  Atom.expr ((run cfg { State.empty with input := Space.singleton a, kb := ctx }).output.atoms)

def superposeBind : Atom → List Atom
  | Atom.expr xs => xs
  | a => [a]

end Metta.StdLib
