-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: CordialMiners.Spec.DisseminationSpec
Layer: Spec
Purpose: Dissemination safety and the priority fair-lane progress core. Dissemination is a liveness and
  performance layer, never a safety override: the receive-path only inserts parent-resolved blocks, so
  it preserves blocklace closure (DISS safety, Invariant K.1), and the accepted blocklace only grows
  (Invariant K.3). The fair-lane non-starvation argument (Theorem K.13) rests on FIFO progress, proved
  here as its combinatorial core.
Imports: CordialMiners.Spec.Blocklace
Trusted boundary: human-reviewed spec
Main exports: diss_fair_lane_served, diss_safety_insert_closed, diss_monotone
Open obligations: baseline/priority dissemination completeness (Theorems K.11/K.15) is conditional
  liveness under the network assumptions K.7-K.10 (network trusted boundary).
-/
import CordialMiners.Spec.Blocklace

namespace CordialMiners

/-- Priority fair-lane progress (the combinatorial core of Theorem K.13): an item enqueued at
    position `k` of a FIFO fair lane reaches the front after `k` dequeues. With a nonzero fair lane,
    every enqueued block is therefore eventually served, so the fair lane does not starve. -/
theorem diss_fair_lane_served {α : Type*} (q : List α) (k : ℕ) :
    (q.drop k).head? = q[k]? := by
  rw [List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero]

variable {P Wave Slot Hash : Type*} [DecidableEq P] [DecidableEq Wave] [DecidableEq Slot]
  [DecidableEq Hash]

/-- DISS safety (Invariant K.1): the receive-path insert of a parent-resolved block preserves parent
    closure, so dissemination never creates an invalid accepted blocklace. -/
theorem diss_safety_insert_closed {L : Blocklace P Wave Slot Hash} {b : Block P Wave Slot Hash}
    (hL : ParentClosed L) (hb : b.parents ⊆ hashesOf L) : ParentClosed (insert b L) :=
  bl_02_insert_parentClosed hL hb

/-- DISS monotonicity (Invariant K.3): without a pruning certificate, the accepted blocklace only
    grows under dissemination. -/
theorem diss_monotone (L : Blocklace P Wave Slot Hash) (b : Block P Wave Slot Hash) :
    L ⊆ insert b L := Finset.subset_insert b L

end CordialMiners
