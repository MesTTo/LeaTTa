/-
Module: CordialMiners.Foundation.Basic
Layer: Foundation
Purpose: Shared foundations for the PoR-weighted Cordial Miners formalization: the participant
  weight type and the rational-threshold type, used by every later layer. Generic, with no protocol
  rules, no Rholang, no MeTTa-IL, and no simulation.
Imports: Mathlib
Trusted boundary: none
Main exports: Weight, Ratio
Open obligations: none
-/
import Mathlib

namespace CordialMiners

/-- A participant weight. Proof-of-Reputation gives each committee member a nonnegative weight, and
    quorum thresholds are weighted sums rather than plain signer counts. -/
abbrev Weight := ℕ

/-- A rational threshold `num / den`, a pair of naturals with a positive denominator. Every threshold
    check compares cross-products, so consensus-critical arithmetic stays in `ℕ` and never touches
    floating point. The blueprint forbids floats for certificate validity. -/
structure Ratio where
  num : ℕ
  den : ℕ
  den_pos : 0 < den

end CordialMiners
