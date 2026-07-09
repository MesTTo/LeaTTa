-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.MorkEncodedSpace
Layer: Proofs
Purpose: Query-refinement laws for the decoded-observation encoded-space model. Scalar query refines
  the decoded `Space`, conjunctive query is the serial scalar-query join, and successful encoded add
  is observationally the same as `Space.insert`.
Imports: MettaHyperonFull.Proofs.MorkCodec, MettaHyperonFull.Core.MorkEncodedSpace
Trusted boundary: none
Main exports: QueryBackend.morkEncodedSpaceBackend_refines_decoded,
  QueryBackend.morkEncodedSpaceBackend_uses_serial_queryMulti,
  MorkEncodedSpace.EncodedSpace.add_refines_insert
Open obligations: concrete PathMap lookup, prepared query, sharding, live grounded filtering, and MM2
  exec readback remain above this decoded-observation model.
-/
import MettaHyperonFull.Proofs.MorkCodec
import MettaHyperonFull.Core.MorkEncodedSpace

namespace Metta

namespace QueryBackend

/-- The encoded-space backend has exactly the scalar-query rows of its decoded observation. -/
theorem morkEncodedSpaceBackend_refines_decoded (s : MorkEncodedSpace.EncodedSpace) :
    RefinesSpace morkEncodedSpaceBackend s s.toSpace := by
  intro _pattern
  rfl

/-- The encoded-space backend's conjunctive query is the serial scalar-query join. -/
theorem morkEncodedSpaceBackend_uses_serial_queryMulti :
    UsesSerialQueryMulti morkEncodedSpaceBackend := by
  intro _state _patterns
  rfl

end QueryBackend

namespace MorkEncodedSpace

namespace EncodedSpace

/-- Adding an encodable atom is observationally the same as inserting it into the decoded space. -/
theorem add_refines_insert {s : EncodedSpace} {a : Atom} {encoded : MorkCodec.EncodedAtom}
    (henc : MorkCodec.encode a = some encoded) :
    (s.add a).toSpace = s.toSpace.insert a := by
  unfold add toSpace decodedAtoms Space.insert
  simp [henc, MorkCodec.decode_encode_eq henc]

/-- Querying after a successful encoded add matches querying after reference-space insertion. -/
theorem query_add_refines_insert {s : EncodedSpace} {a pattern : Atom}
    {encoded : MorkCodec.EncodedAtom}
    (henc : MorkCodec.encode a = some encoded) :
    (s.add a).query pattern = (s.toSpace.insert a).query pattern := by
  unfold query
  rw [show (s.add a).toSpace = s.toSpace.insert a from add_refines_insert henc]

end EncodedSpace

end MorkEncodedSpace

end Metta
