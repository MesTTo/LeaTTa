-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: CordialMiners.Spec.Snapshot
Layer: Spec
Purpose: The committee snapshot, the immutable per-wave parameter object every certificate is validated
  against (weights, total weight, rational threshold). Defines well-formedness, the threshold-heavy
  predicate, and the Byzantine-weight bound under which threshold finality is self-enforcing.
Imports: CordialMiners.Foundation.FinsetWeight
Trusted boundary: human-reviewed spec
Main exports: CommitteeSnapshot, CommitteeSnapshot.WF, CommitteeSnapshot.Heavy,
  CommitteeSnapshot.ByzBound
Open obligations: none
-/
import CordialMiners.Foundation.FinsetWeight

namespace CordialMiners

variable {P : Type*}

/-- A committee snapshot: the finite committee, each member's PoR weight, the total committee weight,
    and the rational threshold. Reputation itself is a structured upstream object; the snapshot records
    only its projection to a weight, which is the parameter the consensus math depends on. -/
structure CommitteeSnapshot (P : Type*) where
  committee : Finset P
  weight : P → Weight
  totalWeight : Weight
  threshold : Ratio

namespace CommitteeSnapshot

/-- A snapshot is well formed when the recorded total weight is the sum of member weights and the
    threshold is strictly between 0 and 1 (so the overlap margin `2θ − 1` is meaningful). -/
def WF (S : CommitteeSnapshot P) : Prop :=
  S.totalWeight = wt S.weight S.committee ∧ 0 < S.threshold.num ∧ S.threshold.num < S.threshold.den

/-- A set of committee members is threshold-heavy: it is within the committee and its weight crosses
    the threshold of the total committee weight. -/
def Heavy (S : CommitteeSnapshot P) (A : Finset P) : Prop :=
  A ⊆ S.committee ∧ thresholdPassed (wt S.weight A) S.totalWeight S.threshold

/-- The Byzantine-weight bound that makes threshold finality self-enforcing: the total weight of the
    non-honest committee members is at most `(2θ − 1)·W`. Stated Nat-safely as
    `wt(C \ honest)·den + W·den ≤ 2·(num·W)`, i.e. `wt(C \ honest) ≤ (2θ − 1)W`. -/
def ByzBound [DecidableEq P] (S : CommitteeSnapshot P) (honest : Finset P) : Prop :=
  wt S.weight (S.committee \ honest) * S.threshold.den + S.totalWeight * S.threshold.den
    ≤ 2 * (S.threshold.num * S.totalWeight)

end CommitteeSnapshot

end CordialMiners
