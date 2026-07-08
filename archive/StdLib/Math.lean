-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

import MettaHyperonFull.Core.Builtins

namespace Metta.StdLib
open Metta

/-- Mathematical builtins are represented by total Lean wrappers returning MeTTa-style status. -/
def add := Builtins.intBin (fun x y => x + y)
def sub := Builtins.intBin (fun x y => x - y)
def mul := Builtins.intBin (fun x y => x * y)
def lt := Builtins.intCmp (fun x y => x < y)
def le := Builtins.intCmp (fun x y => x <= y)
def gt := Builtins.intCmp (fun x y => x > y)
def ge := Builtins.intCmp (fun x y => x >= y)

def absMath : List Atom → ReduceResult
  | [Atom.gnd (Ground.int n)] => ReduceResult.ok [Atom.gnd (Ground.int (if n < 0 then -n else n))]
  | _ => ReduceResult.incorrectArgument "abs-math expects one Int"

end Metta.StdLib
