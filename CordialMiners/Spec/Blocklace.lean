-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: CordialMiners.Spec.Blocklace
Layer: Spec
Purpose: The blocklace, the DAG of signed blocks that Cordial Miners orders. Defines blocks, the
  block-conflict relation (same creator and slot, different hash), the local blocklace with parent
  closure, and the observation relation (reachability through parent pointers). Proves conflict is
  symmetric and irreflexive (BL-06 shape), observation is reflexive and transitive (BL-03), and
  inserting a parent-resolved block preserves parent closure (BL-02).
Imports: CordialMiners.Foundation.Basic
Trusted boundary: human-reviewed spec
Main exports: Block, ConflictBlock, bl_conflict_symm, bl_conflict_irrefl, Blocklace, hashesOf,
  ParentClosed, bl_02_insert_parentClosed, ParentEdge, Observes, bl_03_observes_refl,
  bl_03_observes_trans
Open obligations: acyclicity of the parent graph is kept as a separate abstract predicate (the
  blueprint leaves it a placeholder); the full insertion/buffering state machine is future work.
-/
import CordialMiners.Foundation.Basic

namespace CordialMiners

/-- A signed block: its creator, wave, round, slot, parent hashes, and its own hash. A creator may
    produce at most one non-equivocating block per slot. -/
structure Block (P Wave Slot Hash : Type*) where
  creator : P
  wave : Wave
  round : ℕ
  slot : Slot
  parents : Finset Hash
  blockHash : Hash
deriving DecidableEq

variable {P Wave Slot Hash : Type*}

/-- Two blocks conflict when the same creator produced them in the same slot with different hashes. -/
def ConflictBlock (b c : Block P Wave Slot Hash) : Prop :=
  b.creator = c.creator ∧ b.slot = c.slot ∧ b.blockHash ≠ c.blockHash

/-- Conflict is symmetric. -/
theorem bl_conflict_symm {b c : Block P Wave Slot Hash} (h : ConflictBlock b c) :
    ConflictBlock c b := ⟨h.1.symm, h.2.1.symm, fun e => h.2.2 e.symm⟩

/-- Conflict is irreflexive: a block never conflicts with itself. -/
theorem bl_conflict_irrefl (b : Block P Wave Slot Hash) : ¬ ConflictBlock b b :=
  fun h => h.2.2 rfl

/-- A local blocklace is a finite set of blocks. -/
abbrev Blocklace (P Wave Slot Hash : Type*) := Finset (Block P Wave Slot Hash)

/-- The hashes present in a blocklace. -/
def hashesOf [DecidableEq Hash] (L : Blocklace P Wave Slot Hash) : Finset Hash :=
  L.image Block.blockHash

/-- A blocklace is parent-closed when every block's parent hashes are present in the blocklace. -/
def ParentClosed [DecidableEq Hash] (L : Blocklace P Wave Slot Hash) : Prop :=
  ∀ b ∈ L, ∀ h ∈ b.parents, h ∈ hashesOf L

/-- BL-02: inserting a block whose parents are already present preserves parent closure. -/
theorem bl_02_insert_parentClosed [DecidableEq P] [DecidableEq Wave] [DecidableEq Slot]
    [DecidableEq Hash] {L : Blocklace P Wave Slot Hash} {b : Block P Wave Slot Hash}
    (hL : ParentClosed L) (hb : b.parents ⊆ hashesOf L) : ParentClosed (insert b L) := by
  intro c hc h hh
  have hmono : hashesOf L ⊆ hashesOf (insert b L) := by
    apply Finset.image_subset_image
    exact Finset.subset_insert b L
  rcases Finset.mem_insert.mp hc with rfl | hcL
  · exact hmono (hb hh)
  · exact hmono (hL c hcL h hh)

/-- A direct parent edge: `child` points to `parent` by hash, both in the blocklace. -/
def ParentEdge (L : Blocklace P Wave Slot Hash) (child parent : Block P Wave Slot Hash) : Prop :=
  child ∈ L ∧ parent ∈ L ∧ parent.blockHash ∈ child.parents

/-- Observation: `a` observes `b` by following parent pointers zero or more times. -/
def Observes (L : Blocklace P Wave Slot Hash) (a b : Block P Wave Slot Hash) : Prop :=
  Relation.ReflTransGen (ParentEdge L) a b

/-- BL-03 (reflexivity): every block observes itself. -/
theorem bl_03_observes_refl (L : Blocklace P Wave Slot Hash) (a : Block P Wave Slot Hash) :
    Observes L a a := Relation.ReflTransGen.refl

/-- BL-03 (transitivity): observation composes. -/
theorem bl_03_observes_trans {L : Blocklace P Wave Slot Hash} {a b c : Block P Wave Slot Hash}
    (h₁ : Observes L a b) (h₂ : Observes L b c) : Observes L a c := h₁.trans h₂

end CordialMiners
