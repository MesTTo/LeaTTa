-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.MorkNamedSpaces
Layer: Proofs
Purpose: Same-space visibility and cross-space isolation for MORK backend-level named spaces.
Imports: MettaHyperonFull.Proofs.MorkEncodedSpace, MettaHyperonFull.Core.MorkNamedSpaces
Trusted boundary: none
Main exports: MorkNamedSpaces.NamedSpaces.query_add_same,
  MorkNamedSpaces.NamedSpaces.query_add_other,
  MorkNamedSpaces.NamedSpaces.query_add_same_refines_insert
Open obligations: token resolution, imports, and `&self` evaluation live in the minimal interpreter's
  `World` layer.
-/
import MettaHyperonFull.Proofs.MorkEncodedSpace
import MettaHyperonFull.Core.MorkNamedSpaces

namespace Metta

namespace MorkNamedSpaces

namespace NamedSpaces

/-- Querying the same name after an add sees the updated encoded space. -/
theorem query_add_same (w : NamedSpaces) (name : String) (atom pattern : Atom) :
    (w.addAtom name atom).query name pattern = ((w.spaceOf name).add atom).query pattern := by
  simp [query, addAtom]

/-- Adding to one name does not change query rows for a different name. -/
theorem query_add_other {w : NamedSpaces} {name other : String} {atom pattern : Atom}
    (h : other ≠ name) :
    (w.addAtom name atom).query other pattern = w.query other pattern := by
  simp [query, addAtom, h]

/-- A successful encoded add to one name is observationally reference-space insertion for that name. -/
theorem query_add_same_refines_insert {w : NamedSpaces} {name : String} {atom pattern : Atom}
    {encoded : MorkCodec.EncodedAtom}
    (henc : MorkCodec.encode atom = some encoded) :
    (w.addAtom name atom).query name pattern =
      ((w.spaceOf name).toSpace.insert atom).query pattern := by
  rw [query_add_same]
  exact MorkEncodedSpace.EncodedSpace.query_add_refines_insert henc

end NamedSpaces

end MorkNamedSpaces

end Metta
