-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.MorkEncodedSpace
Layer: Core
Purpose: A decoded-observation model of a MORK-backed space. The state stores encoded atoms, exposes
  the decoded `Space` as its semantic observation, and implements the `QueryBackend` surface through
  that observation.
Imports: MettaHyperonFull.Core.QueryBackend, MettaHyperonFull.Core.MorkCodec
Trusted boundary: none
Main exports: MorkEncodedSpace.EncodedSpace, EncodedSpace.toSpace, EncodedSpace.add,
  EncodedSpace.removeOne, QueryBackend.morkEncodedSpaceBackend
Open obligations: concrete PathMap lookup, prepared queries, sharding, mutable grounded post-filters,
  and MM2 exec effects are later layers over this decoded-observation model.
-/
import MettaHyperonFull.Core.QueryBackend
import MettaHyperonFull.Core.MorkCodec

namespace Metta

namespace MorkEncodedSpace

/-- An encoded-space state. Invalid encoded atoms decode to no observable atom. -/
structure EncodedSpace where
  atoms : List MorkCodec.EncodedAtom
  deriving Repr, BEq, Inhabited

namespace EncodedSpace

def empty : EncodedSpace :=
  ⟨[]⟩

/-- The atom list observed by decoding the encoded store. -/
def decodedAtoms (s : EncodedSpace) : List Atom :=
  s.atoms.filterMap MorkCodec.decode

/-- The reference `Space` observed through decoding. -/
def toSpace (s : EncodedSpace) : Space :=
  ⟨s.decodedAtoms⟩

def query (s : EncodedSpace) (pattern : Atom) : List Bindings :=
  s.toSpace.query pattern

def queryMulti (s : EncodedSpace) (patterns : List Atom) : QueryResult :=
  QueryBackend.serialQueryMulti 0 (fun pattern => s.query pattern) patterns

/-- Add an atom if it fits the codec bounds. Rejected atoms are not observed. -/
def add (s : EncodedSpace) (a : Atom) : EncodedSpace :=
  match MorkCodec.encode a with
  | some encoded => ⟨encoded :: s.atoms⟩
  | none => s

/-- True when an encoded atom decodes to a structurally equal atom. -/
def decodesAs (encoded : MorkCodec.EncodedAtom) (a : Atom) : Bool :=
  match MorkCodec.decode encoded with
  | some decoded => decoded == a
  | none => false

/-- Remove the first encoded atom whose decoded observation is structurally equal to `a`. -/
def removeFirstDecoded (a : Atom) : List MorkCodec.EncodedAtom → List MorkCodec.EncodedAtom
  | [] => []
  | encoded :: rest =>
      if decodesAs encoded a then
        rest
      else
        encoded :: removeFirstDecoded a rest

/-- Remove one decoded atom copy if a matching encoded entry exists. -/
def removeOne (s : EncodedSpace) (a : Atom) : EncodedSpace :=
  ⟨removeFirstDecoded a s.atoms⟩

end EncodedSpace

end MorkEncodedSpace

namespace QueryBackend

/-- The encoded-space decoded-observation backend. -/
def morkEncodedSpaceBackend : QueryBackend where
  State := MorkEncodedSpace.EncodedSpace
  capabilities := Capabilities.scalarAndJoin
  generation := fun _ => 0
  query := fun s pattern => QueryResult.completeAt 0 (s.query pattern)
  queryMulti := MorkEncodedSpace.EncodedSpace.queryMulti
  add := MorkEncodedSpace.EncodedSpace.add
  removeOne := MorkEncodedSpace.EncodedSpace.removeOne
  snapshot := id
  restore := fun snap _ => snap

end QueryBackend

end Metta
