-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.MorkCodec
Layer: Core
Purpose: A small executable model of the MORK atom codec boundary. It records the proof-facing byte
  shape that matters first: bounded symbols and arity, variable slots, repeated variable references,
  and a side table that recovers caller variable names on decode.
Imports: MettaHyperonFull.Core.Atom
Trusted boundary: none
Main exports: MorkCodec.maxField, MorkCodec.maxVars, MorkCodec.Code, MorkCodec.EncodedAtom,
  MorkCodec.indexOf?, MorkCodec.encodeWithSlots, MorkCodec.encode, MorkCodec.decodeWith,
  MorkCodec.decode, MorkCodec.varSlots
Open obligations: this is a logical codec model, not the concrete PathMap byte trie. Mutable grounded
  identity, live-value filtering, NewVar/VarRef prefix-extension proofs, and encoded-backend query
  refinement are stated above this layer.
-/
import MettaHyperonFull.Core.Atom

namespace Metta

namespace MorkCodec

/-- MORK's arity and symbol-size byte fields are six bits wide. -/
def maxField : Nat := 63

/-- The current byte codec keeps at most sixty-four variable slots per atom. -/
def maxVars : Nat := 64

/-- The proof-facing shape of the encoded MORK expression. -/
inductive Code where
  | sym : String → Code
  | gnd : Ground → Code
  | var : Nat → Code
  | expr : List Code → Code
  deriving Repr, BEq, Inhabited

/-- An encoded atom plus the side table used to recover source variable names. -/
structure EncodedAtom where
  code : Code
  vars : List VarName
  deriving Repr, BEq, Inhabited

/-- Total list lookup used by the codec model. -/
def getAt? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => getAt? xs n

/-- First index of `x` in `xs`, if present. -/
def indexOf? (x : VarName) : List VarName → Option Nat
  | [] => none
  | y :: ys =>
      if x == y then
        some 0
      else
        (indexOf? x ys).map Nat.succ

mutual

/-- Encode an atom against an already chosen variable side table. -/
def encodeWithSlots (slots : List VarName) : Atom → Option Code
  | Atom.sym s =>
      if s.length ≤ maxField then
        some (Code.sym s)
      else
        none
  | Atom.var x =>
      match indexOf? x slots with
      | some i => some (Code.var i)
      | none => none
  | Atom.gnd g => some (Code.gnd g)
  | Atom.expr xs =>
      if xs.length ≤ maxField then
        match encodeListWithSlots slots xs with
        | some codes => some (Code.expr codes)
        | none => none
      else
        none

/-- Encode child atoms against the same variable side table. -/
def encodeListWithSlots (slots : List VarName) : List Atom → Option (List Code)
  | [] => some []
  | x :: xs =>
      match encodeWithSlots slots x, encodeListWithSlots slots xs with
      | some code, some codes => some (code :: codes)
      | _, _ => none

end

mutual

/-- Decode a code node using its variable side table. -/
def decodeWith (slots : List VarName) : Code → Option Atom
  | Code.sym s => some (Atom.sym s)
  | Code.var i => (getAt? slots i).map Atom.var
  | Code.gnd g => some (Atom.gnd g)
  | Code.expr codes =>
      match decodeListWith slots codes with
      | some atoms => some (Atom.expr atoms)
      | none => none

/-- Decode child code nodes using the same variable side table. -/
def decodeListWith (slots : List VarName) : List Code → Option (List Atom)
  | [] => some []
  | code :: codes =>
      match decodeWith slots code, decodeListWith slots codes with
      | some atom, some atoms => some (atom :: atoms)
      | _, _ => none

end

/-- Encode one atom. This first slice uses occurrence slots, so the variable bound is conservative. -/
def encode (a : Atom) : Option EncodedAtom :=
  let slots := Atom.vars a
  if slots.length ≤ maxVars then
    match encodeWithSlots slots a with
    | some code => some { code, vars := slots }
    | none => none
  else
    none

/-- Decode one encoded atom. -/
def decode (e : EncodedAtom) : Option Atom :=
  decodeWith e.vars e.code

/-- The variable side table of a successfully encoded atom. -/
def varSlots (e : EncodedAtom) : List VarName :=
  e.vars

/-- Repeated variables point at the first side-table slot for that name. -/
example :
    encode (Atom.expr [Atom.var "x", Atom.var "x"]) =
      some { code := Code.expr [Code.var 0, Code.var 0], vars := ["x", "x"] } := by
  simp [encode, Atom.vars, encodeWithSlots, encodeListWithSlots, indexOf?, maxVars, maxField]

/-- The codec preserves the caller's variable name through a repeated-variable round trip. -/
example :
    (match encode (Atom.expr [Atom.var "x", Atom.var "x"]) with
    | some encoded => decode encoded
    | none => none) =
      some (Atom.expr [Atom.var "x", Atom.var "x"]) := by
  simp [encode, Atom.vars, encodeWithSlots, encodeListWithSlots, decode, decodeWith, decodeListWith,
    getAt?, indexOf?, maxVars, maxField]

end MorkCodec

end Metta
