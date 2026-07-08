-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: CordialMiners.Ref.FinalityPermanence
Layer: Ref
Purpose: Reach the canonical primitive behind leader safety: finality permanence. A wave once finalized
  stays finalized as the blocklace grows. We define the finalized-wave count as the largest consecutive
  finalized prefix length (within a bound), and prove it is monotone in the blocklace from two facts:
  finality permanence (Final L1 w -> Final L2 w when L1 subset L2) and a monotone bound (the block count
  works). This discharges the scalar leader-safety hypothesis of Ref.FinalizedAnchors, so the whole
  safety edifice rests on three named facts: the Byzantine-weight bound, honest non-equivocation, and
  finality permanence.
Imports: CordialMiners.Ref.FinalizedAnchors
Trusted boundary: none (fully proved). Finality permanence is the residual primitive, and it is exactly
  the blocklace-only-grows discipline applied to finality certificates.
Main exports: findGreatest_mono_pred, finalCountOf, finalCountOf_monotone
Open obligations: none at this layer.
-/
import CordialMiners.Ref.FinalizedAnchors

namespace CordialMiners

/-- findGreatest is monotone in the predicate: a weaker predicate has a greater (or equal) maximum. -/
theorem findGreatest_mono_pred {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ k, P k → Q k) (n : ℕ) : Nat.findGreatest P n ≤ Nat.findGreatest Q n := by
  rcases Nat.eq_zero_or_pos (Nat.findGreatest P n) with hz | hpos
  · rw [hz]; exact Nat.zero_le _
  · exact Nat.le_findGreatest (Nat.findGreatest_le n)
      (hPQ _ (Nat.findGreatest_of_ne_zero rfl hpos.ne'))

variable {P Wave Slot Hash : Type*}

/-- The finalized-wave count: the largest prefix length `k` (within `bound L`) such that every wave below
    `k` is finalized in `L`. -/
def finalCountOf (Final : Blocklace P Wave Slot Hash → ℕ → Prop) [∀ L w, Decidable (Final L w)]
    (bound : Blocklace P Wave Slot Hash → ℕ) (L : Blocklace P Wave Slot Hash) : ℕ :=
  Nat.findGreatest (fun k => ∀ w < k, Final L w) (bound L)

/-- The finalized-wave count is monotone in the blocklace, given finality permanence (a finalized wave
    stays finalized as the blocklace grows) and a monotone bound. This is the scalar leader-safety fact
    of Ref.FinalizedAnchors, now derived from the canonical finality primitive. -/
theorem finalCountOf_monotone (Final : Blocklace P Wave Slot Hash → ℕ → Prop)
    [∀ L w, Decidable (Final L w)] (bound : Blocklace P Wave Slot Hash → ℕ)
    (hperm : ∀ (w : ℕ) {L₁ L₂ : Blocklace P Wave Slot Hash}, L₁ ⊆ L₂ → Final L₁ w → Final L₂ w)
    (hbound : ∀ {L₁ L₂ : Blocklace P Wave Slot Hash}, L₁ ⊆ L₂ → bound L₁ ≤ bound L₂)
    {L₁ L₂ : Blocklace P Wave Slot Hash} (hsub : L₁ ⊆ L₂) :
    finalCountOf Final bound L₁ ≤ finalCountOf Final bound L₂ := by
  unfold finalCountOf
  refine le_trans (findGreatest_mono_pred (fun k hk w hw => hperm w hsub (hk w hw)) (bound L₁))
    (Nat.findGreatest_mono_right _ (hbound hsub))

end CordialMiners
