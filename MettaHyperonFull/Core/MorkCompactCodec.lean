-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.MorkCompactCodec
Layer: Core
Purpose: Compact MORK variable trace model. First occurrences emit `newVar`; later occurrences emit
  `varRef(slot)`, where `slot` points back into the first-occurrence side table.
Imports: MettaHyperonFull.Core.MorkCodec
Trusted boundary: none
Main exports: MorkCompactCodec.Code, MorkCompactCodec.EncodedAtom, MorkCompactCodec.encodeAt,
  MorkCompactCodec.encode, MorkCompactCodec.decodeAt, MorkCompactCodec.decode
Open obligations: this models the compact variable trace. Concrete byte values and long tags remain
  below this proof-facing representation.
-/
import MettaHyperonFull.Core.MorkCodec

namespace Metta

namespace MorkCompactCodec

/-- Compact proof-facing MORK code with explicit NewVar and VarRef constructors. -/
inductive Code where
  | sym : String → Code
  | gnd : Ground → Code
  | newVar : Code
  | varRef : Nat → Code
  | expr : List Code → Code
  deriving Repr, BEq, Inhabited

/-- Compact encoded atom plus its first-occurrence variable side table. -/
structure EncodedAtom where
  code : Code
  vars : List VarName
  deriving Repr, BEq, Inhabited

mutual

/-- Encode one atom, threading the first-occurrence side table. -/
def encodeAt (seen : List VarName) : Atom → Option (Code × List VarName)
  | Atom.sym s =>
      if s.length ≤ MorkCodec.maxField then
        some (Code.sym s, seen)
      else
        none
  | Atom.var x =>
      match MorkCodec.indexOf? x seen with
      | some i => some (Code.varRef i, seen)
      | none =>
          if seen.length < MorkCodec.maxVars then
            some (Code.newVar, seen ++ [x])
          else
            none
  | Atom.gnd g => some (Code.gnd g, seen)
  | Atom.expr xs =>
      if xs.length ≤ MorkCodec.maxField then
        match encodeListAt seen xs with
        | some (codes, seen') => some (Code.expr codes, seen')
        | none => none
      else
        none

/-- Encode child atoms, threading the same first-occurrence side table. -/
def encodeListAt (seen : List VarName) : List Atom → Option (List Code × List VarName)
  | [] => some ([], seen)
  | x :: xs =>
      match encodeAt seen x with
      | some (code, seen') =>
          match encodeListAt seen' xs with
          | some (codes, seen'') => some (code :: codes, seen'')
          | none => none
      | none => none

end

mutual

/-- Decode one compact code node, using `next` as the NewVar counter. -/
def decodeAt (slots : List VarName) : Nat → Code → Option (Atom × Nat)
  | next, Code.sym s => some (Atom.sym s, next)
  | next, Code.gnd g => some (Atom.gnd g, next)
  | next, Code.newVar =>
      match MorkCodec.getAt? slots next with
      | some x => some (Atom.var x, next + 1)
      | none => none
  | next, Code.varRef i =>
      match MorkCodec.getAt? slots i with
      | some x => some (Atom.var x, next)
      | none => none
  | next, Code.expr codes =>
      match decodeListAt slots next codes with
      | some (atoms, next') => some (Atom.expr atoms, next')
      | none => none

/-- Decode child code nodes with the same final variable side table. -/
def decodeListAt (slots : List VarName) : Nat → List Code → Option (List Atom × Nat)
  | next, [] => some ([], next)
  | next, code :: codes =>
      match decodeAt slots next code with
      | some (atom, next') =>
          match decodeListAt slots next' codes with
          | some (atoms, next'') => some (atom :: atoms, next'')
          | none => none
      | none => none

end

/-- Encode one atom from an empty side table. -/
def encode (a : Atom) : Option EncodedAtom :=
  match encodeAt [] a with
  | some (code, vars) => some { code, vars }
  | none => none

/-- Decode one compact encoded atom. -/
def decode (encoded : EncodedAtom) : Option Atom :=
  match decodeAt encoded.vars 0 encoded.code with
  | some (atom, _) => some atom
  | none => none

end MorkCompactCodec

end Metta
