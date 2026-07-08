-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: CordialMiners.Ref.FinalizedAnchors
Layer: Ref
Purpose: Derive the leader-safety prefix fact (AnchorPrefixMonotone) from a more primitive finalization
  invariant. The anchor sequence is the first `finalCount L` canonical leaders, where `finalCount L` is
  how many consecutive waves (from wave zero) are finalized in `L`. Finality is permanent and proceeds in
  wave order, so this count only grows as the blocklace grows. leaderList builds the cumulative leader
  list, and we prove it is prefix-monotone in the count, hence the anchor sequence is prefix-monotone in
  the blocklace. The leader-safety hypothesis is thereby reduced to a single scalar fact: finalCount is
  monotone.
Imports: CordialMiners.Ref.AnchoredOrder
Trusted boundary: none (fully proved). The monotonicity of finalCount is the residual primitive fact:
  finality permanence (a finalized wave stays finalized) plus sequential finalization (waves finalize in
  order) give it, but those rest on the protocol's finality machinery, modelled here by the hypothesis.
Main exports: leaderList, leaderList_prefix_of_le, finalizedAnchors, finalizedAnchors_prefixMonotone
Open obligations: none at this layer.
-/
import CordialMiners.Ref.AnchoredOrder

namespace CordialMiners

variable {Hash : Type*}

/-- The cumulative leader list: the first `k` canonical leaders, in wave order. -/
def leaderList (leaderOf : ℕ → Hash) : ℕ → List Hash
  | 0 => []
  | k + 1 => leaderList leaderOf k ++ [leaderOf k]

/-- The cumulative leader list is prefix-monotone in its length: more finalized waves give a longer
    list that extends the shorter one, never reordering it. -/
theorem leaderList_prefix_of_le (leaderOf : ℕ → Hash) {m : ℕ} :
    ∀ {n : ℕ}, m ≤ n → leaderList leaderOf m <+: leaderList leaderOf n := by
  intro n
  induction n with
  | zero => intro h; rw [Nat.le_zero.mp h]
  | succ n ih =>
    intro h
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · subst heq; exact List.prefix_rfl
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (by rw [leaderList]; exact List.prefix_append _ _)

variable {P Wave Slot Hash : Type*}

/-- The finalized-anchor sequence: the first `finalCount L` canonical leaders, where `finalCount L` is
    the number of consecutively finalized waves in `L`. -/
def finalizedAnchors (finalCount : Blocklace P Wave Slot Hash → ℕ) (leaderOf : ℕ → Hash) :
    Blocklace P Wave Slot Hash → List Hash := fun L => leaderList leaderOf (finalCount L)

/-- Leader safety derived: if the finalized-wave count is monotone in the blocklace (finality
    permanence plus wave-ordered finalization), the anchor sequence is prefix-monotone. This reduces
    the leader-safety hypothesis to one scalar fact. -/
theorem finalizedAnchors_prefixMonotone (finalCount : Blocklace P Wave Slot Hash → ℕ)
    (leaderOf : ℕ → Hash)
    (hcount : ∀ {L₁ L₂ : Blocklace P Wave Slot Hash}, L₁ ⊆ L₂ → finalCount L₁ ≤ finalCount L₂) :
    AnchorPrefixMonotone (finalizedAnchors finalCount leaderOf) :=
  fun hsub => leaderList_prefix_of_le leaderOf (hcount hsub)

end CordialMiners
