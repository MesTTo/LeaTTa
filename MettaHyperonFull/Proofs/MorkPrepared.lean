-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.MorkPrepared
Layer: Proofs
Purpose: Snapshot and prepared-query equivalence laws for the MORK decoded-observation backend.
Imports: MettaHyperonFull.Proofs.MorkEncodedSpace, MettaHyperonFull.Core.MorkPrepared
Trusted boundary: none
Main exports: MorkPrepared.snapshot_query_eq, MorkPrepared.snapshot_count_eq,
  MorkPrepared.prepared_count_eq
Open obligations: parallelism, concrete buffer reuse, and registry-free snapshot restrictions are
  runtime implementation concerns above these semantic laws.
-/
import MettaHyperonFull.Proofs.MorkEncodedSpace
import MettaHyperonFull.Core.MorkPrepared

namespace Metta

namespace MorkPrepared

/-- Querying a fresh snapshot is the same as querying the encoded space it freezes. -/
theorem snapshot_query_eq (s : MorkEncodedSpace.EncodedSpace) (pattern : Atom) :
    (snapshot s).query pattern = s.query pattern := rfl

/-- Counting a fresh snapshot is the length of the ordinary query rows. -/
theorem snapshot_count_eq (s : MorkEncodedSpace.EncodedSpace) (pattern : Atom) :
    (snapshot s).count pattern = (s.query pattern).length := rfl

/-- Prepared count equals ordinary count on the same snapshot and pattern. -/
theorem prepared_count_eq (snap : Snapshot) (pattern : Atom) :
    snap.countPrepared (prepare pattern) = snap.count pattern := rfl

end MorkPrepared

end Metta
