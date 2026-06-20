/-
Module: CordialMiners.Foundation.FinsetWeight
Layer: Foundation
Purpose: Weighted finite sets and the weighted-overlap safety arithmetic. This is the mathematical
  core of PoR-weighted threshold finality: two threshold-heavy committee subsets must overlap in
  weight, which is what forces an honest signer into any pair of conflicting certificates.
Imports: CordialMiners.Foundation.Basic
Trusted boundary: none
Main exports: wt, thresholdPassed, thresholdPassedBool, found_03_weight_mono,
  found_04_weight_inclusion_exclusion, found_05_weighted_overlap
Open obligations: none
-/
import CordialMiners.Foundation.Basic

namespace CordialMiners

variable {P : Type*}

/-- The total weight of a finite participant set under a weight function. The PoR analogue of "how
    many signers", weighted by reputation. -/
def wt (w : P → Weight) (A : Finset P) : Weight := ∑ p ∈ A, w p

/-- A weighted set of total weight `R` crosses the threshold `θ` of committee weight `W`. Stated by
    cross-product so the check stays in `ℕ`: `θ.num * W < R * θ.den` reads as `R / W > θ.num / θ.den`. -/
def thresholdPassed (R W : Weight) (θ : Ratio) : Prop := θ.num * W < R * θ.den

/-- The decidable Boolean form of `thresholdPassed`, for executable reducers. -/
def thresholdPassedBool (R W : Weight) (θ : Ratio) : Bool := decide (θ.num * W < R * θ.den)

/-- Obligation D.3: the Boolean threshold check reflects the propositional one. -/
theorem thresholdPassedBool_iff (R W : Weight) (θ : Ratio) :
    thresholdPassedBool R W θ = true ↔ thresholdPassed R W θ := by
  simp [thresholdPassedBool, thresholdPassed]

/-- FOUND-03: total weight is monotone in the set. -/
theorem found_03_weight_mono (w : P → Weight) {A B : Finset P} (h : A ⊆ B) :
    wt w A ≤ wt w B := by
  simp only [wt]; exact Finset.sum_le_sum_of_subset h

/-- FOUND-04: weighted inclusion-exclusion, stated additively so it stays in `ℕ` with no subtraction. -/
theorem found_04_weight_inclusion_exclusion [DecidableEq P] (w : P → Weight) (A B : Finset P) :
    wt w (A ∪ B) + wt w (A ∩ B) = wt w A + wt w B := by
  simp only [wt]; exact Finset.sum_union_inter

/-- The pure linear-arithmetic core of the overlap lemma, over plain naturals. Factoring it out lets
    `omega` run on clean variables, free of the product terms it does not reliably atomize. -/
private theorem overlap_arith {a b c d e f : ℕ}
    (hA : b < a) (hB : b < c) (key : f + d = a + c) (hud : f ≤ e) : 2 * b < d + e := by
  omega

/-- FOUND-05: the weighted-overlap lemma, the heart of PoR threshold-finality safety. If two
    committee subsets `A` and `B` of `C` are each threshold-heavy for `θ`, their intersection carries
    more than `(2θ - 1)` of the committee weight. Stated Nat-safely as
    `2 (θ.num · W) < wt(A ∩ B) · θ.den + W · θ.den`, which is exactly `wt(A ∩ B) > (2θ - 1) W`. -/
theorem found_05_weighted_overlap [DecidableEq P] (w : P → Weight) {C A B : Finset P} (θ : Ratio)
    (hAC : A ⊆ C) (hBC : B ⊆ C)
    (hA : thresholdPassed (wt w A) (wt w C) θ)
    (hB : thresholdPassed (wt w B) (wt w C) θ) :
    2 * (θ.num * wt w C) < wt w (A ∩ B) * θ.den + wt w C * θ.den := by
  unfold thresholdPassed at hA hB
  have key2 : wt w (A ∪ B) * θ.den + wt w (A ∩ B) * θ.den
            = wt w A * θ.den + wt w B * θ.den := by
    rw [← add_mul, ← add_mul, found_04_weight_inclusion_exclusion]
  have hud : wt w (A ∪ B) * θ.den ≤ wt w C * θ.den := by
    gcongr
    exact found_03_weight_mono w (Finset.union_subset hAC hBC)
  exact overlap_arith hA hB key2 hud

end CordialMiners
