-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.MorkPrepared
Layer: Core
Purpose: Read-only snapshot and prepared-query model for the MORK decoded-observation backend.
  Snapshots freeze an encoded-space state. Prepared queries cache the pattern, not the semantics.
Imports: MettaHyperonFull.Core.MorkEncodedSpace
Trusted boundary: none
Main exports: MorkPrepared.Snapshot, MorkPrepared.PreparedQuery, MorkPrepared.snapshot,
  MorkPrepared.prepare, MorkPrepared.Snapshot.query, MorkPrepared.Snapshot.count,
  MorkPrepared.Snapshot.countPrepared
Open obligations: this models the semantic contract of snapshots and prepared queries, not the
  concrete byte buffer reuse in the Rust runtime.
-/
import MettaHyperonFull.Core.MorkEncodedSpace

namespace Metta

namespace MorkPrepared

/-- A read-only view of an encoded space. -/
structure Snapshot where
  state : MorkEncodedSpace.EncodedSpace
  deriving Repr, BEq, Inhabited

/-- A query whose pattern has been prepared for repeated use. -/
structure PreparedQuery where
  pattern : Atom
  deriving Repr, BEq, Inhabited

/-- Freeze the current encoded-space state for read-only querying. -/
def snapshot (s : MorkEncodedSpace.EncodedSpace) : Snapshot :=
  ⟨s⟩

/-- Prepare a pattern for repeated count queries. -/
def prepare (pattern : Atom) : PreparedQuery :=
  ⟨pattern⟩

namespace Snapshot

def query (snap : Snapshot) (pattern : Atom) : List Bindings :=
  snap.state.query pattern

def count (snap : Snapshot) (pattern : Atom) : Nat :=
  (snap.query pattern).length

def countPrepared (snap : Snapshot) (prepared : PreparedQuery) : Nat :=
  snap.count prepared.pattern

end Snapshot

end MorkPrepared

end Metta
