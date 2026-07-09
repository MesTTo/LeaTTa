-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.MorkSharded
Layer: Proofs
Purpose: Sharded query/count equivalence for finite decoded-observation MORK spaces.
Imports: MettaHyperonFull.Proofs.MorkEncodedSpace, MettaHyperonFull.Core.MorkSharded
Trusted boundary: none
Main exports: MorkSharded.ShardedSpace.queryByShards_eq_query,
  MorkSharded.ShardedSpace.countByShards_eq_count
Open obligations: shard hash routing and parallel scheduling are implementation refinements.
-/
import MettaHyperonFull.Proofs.MorkEncodedSpace
import MettaHyperonFull.Core.MorkSharded

namespace Metta

namespace MorkSharded

namespace ShardedSpace

/-- Reassociate shard decoding with row production. -/
theorem flatMap_decodedAtoms_query (shards : List MorkEncodedSpace.EncodedSpace)
    (pattern : Atom) :
    shards.flatMap (fun shard => shard.decodedAtoms.flatMap (fun atom => matchAtoms pattern atom)) =
      (shards.flatMap (fun shard => shard.decodedAtoms)).flatMap (fun atom => matchAtoms pattern atom) := by
  induction shards with
  | nil =>
      rfl
  | cons shard rest ih =>
      simp [ih, List.flatMap_append]

/-- Shard-local row concatenation equals querying the unsharded decoded observation. -/
theorem queryByShards_eq_query (s : ShardedSpace) (pattern : Atom) :
    s.queryByShards pattern = s.query pattern := by
  cases s with
  | mk shards =>
      simp [queryByShards, query, toSpace, decodedAtoms, MorkEncodedSpace.EncodedSpace.query,
        MorkEncodedSpace.EncodedSpace.toSpace, Space.query, flatMap_decodedAtoms_query]

/-- Counting shard-local rows equals counting rows over the unsharded decoded observation. -/
theorem countByShards_eq_count (s : ShardedSpace) (pattern : Atom) :
    s.countByShards pattern = s.count pattern := by
  unfold countByShards count
  rw [queryByShards_eq_query]

end ShardedSpace

end MorkSharded

end Metta
