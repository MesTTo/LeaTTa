-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.MorkSharded
Layer: Core
Purpose: Finite sharded decoded-observation model for MORK spaces. A sharded query is the
  concatenation of the shard-local query rows, and the unsharded observation is the concatenation of
  the decoded shard atoms.
Imports: MettaHyperonFull.Core.MorkEncodedSpace
Trusted boundary: none
Main exports: MorkSharded.ShardedSpace, ShardedSpace.toSpace, ShardedSpace.query,
  ShardedSpace.queryByShards, ShardedSpace.count, ShardedSpace.countByShards
Open obligations: this models finite shard semantics. Hash-prefix routing and parallel scheduling are
  implementation layers above it.
-/
import MettaHyperonFull.Core.MorkEncodedSpace

namespace Metta

namespace MorkSharded

/-- A finite family of encoded-space shards. -/
structure ShardedSpace where
  shards : List MorkEncodedSpace.EncodedSpace
  deriving Repr, BEq, Inhabited

namespace ShardedSpace

def empty : ShardedSpace :=
  ⟨[]⟩

/-- The decoded atom list observed by concatenating every shard. -/
def decodedAtoms (s : ShardedSpace) : List Atom :=
  s.shards.flatMap (fun shard => shard.toSpace.atoms)

/-- The unsharded decoded observation of all shards. -/
def toSpace (s : ShardedSpace) : Space :=
  ⟨s.decodedAtoms⟩

/-- Query through the unsharded decoded observation. -/
def query (s : ShardedSpace) (pattern : Atom) : List Bindings :=
  s.toSpace.query pattern

/-- Query shard-by-shard and concatenate the rows. -/
def queryByShards (s : ShardedSpace) (pattern : Atom) : List Bindings :=
  s.shards.flatMap (fun shard => shard.query pattern)

def count (s : ShardedSpace) (pattern : Atom) : Nat :=
  (s.query pattern).length

def countByShards (s : ShardedSpace) (pattern : Atom) : Nat :=
  (s.queryByShards pattern).length

end ShardedSpace

end MorkSharded

end Metta
