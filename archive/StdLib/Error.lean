-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

import MettaHyperonFull.Core.Result

namespace Metta.StdLib
open Metta

def error (a : Atom) (msg : String) : Atom := Atom.expr [Atom.sym "Error", a, Atom.gnd (Ground.str msg)]
def ifError (a fallback : Atom) : Atom := if Atom.isError a then fallback else a
def returnOnError (a : Atom) : Atom := if Atom.isError a then a else Atom.expr [Atom.sym "return", a]

end Metta.StdLib
