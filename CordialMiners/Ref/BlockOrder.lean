-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: CordialMiners.Ref.BlockOrder
Layer: Ref
Purpose: Wire the verified generic topological sort to the actual blocklace. blockDeps reads the parent
  graph a blocklace induces on hashes, and blockOrder = topoSort over the present hashes by that graph.
  blockOrder is a concrete Ordering P Wave Slot Hash. The within-snapshot guarantees transfer directly:
  the order is deterministic, duplicate-free, output-valid, complete (under a round-style rank), and
  topologically sound, so a block's blocklace-parents are never placed after it (the causal-consistency
  property, connected to the protocol's ParentEdge relation). Note blockOrder is not output-monotone as
  the blocklace grows (raw topological sort can reorder); cross-snapshot consistency is the anchored
  ordering of Ref.AnchoredOrder.
Imports: CordialMiners.Ref.TauOrder, CordialMiners.Spec.TauOrderSpec
Trusted boundary: none (fully proved)
Main exports: blockDeps, blockOrder, blockOrder_nodup, blockOrder_subset, blockOrder_topoSorted,
  blockOrder_deterministic, blockOrder_complete, parentEdge_mem_blockDeps,
  blockOrder_parentEdge_not_after
Open obligations: output-monotonicity is not expected of blockOrder; the monotone cross-snapshot order
  is anchoredOrder (Ref.AnchoredOrder).
-/
import CordialMiners.Ref.TauOrder
import CordialMiners.Spec.TauOrderSpec

namespace CordialMiners

variable {P Wave Slot Hash : Type*}

/-- The dependency graph a blocklace induces on hashes: the parent hashes of the block(s) carrying `h`.
    In a hash-unique blocklace this is just the parents of the one block with hash `h`. -/
def blockDeps [DecidableEq Hash] (L : Blocklace P Wave Slot Hash) (h : Hash) : Finset Hash :=
  (L.filter (fun b => b.blockHash = h)).biUnion Block.parents

variable [LinearOrder Hash]

/-- The concrete blocklace ordering: topologically sort the present hashes by the parent graph, with
    canonical least-first tie-breaking. As a function of the blocklace it is an `Ordering`, realized by
    the verified `topoSort`. -/
def blockOrder (L : Blocklace P Wave Slot Hash) : List Hash :=
  topoSort (hashesOf L) (blockDeps L)

/-- `blockOrder` inhabits the abstract ordering type. -/
example : Ordering P Wave Slot Hash := blockOrder

/-- The order has no duplicate positions. -/
theorem blockOrder_nodup (L : Blocklace P Wave Slot Hash) : (blockOrder L).Nodup :=
  topoSort_nodup _ _

/-- Output-validity: every hash in the order is present in the blocklace. -/
theorem blockOrder_subset {L : Blocklace P Wave Slot Hash} {h : Hash} (hh : h ∈ blockOrder L) :
    h ∈ hashesOf L := topoSort_subset _ _ hh

/-- The order is topologically sorted for the parent graph: no parent hash is placed after the hash
    that depends on it. -/
theorem blockOrder_topoSorted (L : Blocklace P Wave Slot Hash) :
    TopoSorted (blockDeps L) (blockOrder L) := topoSort_topoSorted _ _

/-- Determinism: equal blocklaces give equal orders (the ordering is a pure function). -/
theorem blockOrder_deterministic {L₁ L₂ : Blocklace P Wave Slot Hash} (h : L₁ = L₂) :
    blockOrder L₁ = blockOrder L₂ := by rw [h]

/-- Completeness: under a strict rank on the parent graph (a parent ranks below its child, e.g. by
    round), every present hash appears in the order. With blockOrder_subset and blockOrder_nodup, the
    order lists exactly the present hashes, once each. -/
theorem blockOrder_complete {L : Blocklace P Wave Slot Hash} {rank : Hash → ℕ}
    (hrank : ∀ h, ∀ p ∈ blockDeps L h, rank p < rank h) {h : Hash} (hh : h ∈ hashesOf L) :
    h ∈ blockOrder L := topoSort_complete _ _ hrank hh

/-- A real parent edge becomes a dependency in the induced graph: if `child` points to `parent`, then
    `parent`'s hash is a dependency of `child`'s hash. -/
theorem parentEdge_mem_blockDeps [DecidableEq P] [DecidableEq Wave] [DecidableEq Slot]
    {L : Blocklace P Wave Slot Hash} {child parent : Block P Wave Slot Hash}
    (h : ParentEdge L child parent) : parent.blockHash ∈ blockDeps L child.blockHash := by
  obtain ⟨hchild, _, hpar⟩ := h
  rw [blockDeps, Finset.mem_biUnion]
  exact ⟨child, Finset.mem_filter.mpr ⟨hchild, rfl⟩, hpar⟩

/-- Causal consistency for real parent edges: wherever a block's hash sits in the order, the hash of any
    block it points to as a parent is never after it. The published order respects the blocklace DAG. -/
theorem blockOrder_parentEdge_not_after [DecidableEq P] [DecidableEq Wave] [DecidableEq Slot]
    {L : Blocklace P Wave Slot Hash} {child parent : Block P Wave Slot Hash}
    (h : ParentEdge L child parent) {l₁ l₂ : List Hash}
    (hsplit : blockOrder L = l₁ ++ child.blockHash :: l₂) : parent.blockHash ∉ l₂ :=
  blockOrder_topoSorted L l₁ child.blockHash l₂ hsplit parent.blockHash (parentEdge_mem_blockDeps h)

end CordialMiners
