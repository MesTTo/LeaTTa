-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

import MettaHyperonFull.Core.Space

namespace Metta.StdLib
open Metta

def addAtom (s : Space) (a : Atom) : Space × Atom := (Space.insert s a, Atom.unit)
def removeAtom (s : Space) (a : Atom) : Space × Atom := (Space.removeOne s a, Atom.unit)
def getAtoms (s : Space) : Atom := Atom.expr s.atoms
def matchSpace (s : Space) (p tmpl : Atom) : List Atom := s.transform p tmpl
def getTypeSpace (s : Space) (a : Atom) : List Atom := s.typeAssignments a

def newSpace : Space := Space.empty

end Metta.StdLib
