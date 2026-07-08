-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: CordialMiners.Spec.SchedulerSpec
Layer: Spec
Purpose: Multi-wave scheduler safety. The scheduler never makes consensus unsafe: it publishes output
  only when the new prefix extends the old, so published output forms a prefix chain (output-prefix
  safety, Invariant L.9 / Theorem L.19). The bounded-service argument (Theorem L.14) rests on a
  positive fairness quantum, whose core is proved here.
Imports: CordialMiners.Foundation.Prefix
Trusted boundary: human-reviewed spec
Main exports: safePublish, sched_output_prefix_safe, sched_credit_reaches
Open obligations: wave non-starvation and persistent task completion (Theorems L.13/L.15) are
  conditional liveness under the scheduler-fairness assumptions (scheduler trusted boundary).
-/
import CordialMiners.Foundation.Prefix

namespace CordialMiners

/-- A safe publish accepts an update only if it extends the current published prefix; otherwise it
    keeps the current output (the implementation would emit a violation). -/
def safePublish {α : Type*} [DecidableEq α] (old new : List α) : List α :=
  if old <+: new then new else old

/-- Output-prefix safety (Invariant L.9 / Theorem L.19): a safe publish never regresses, so the stream
    of published outputs forms a chain under the prefix order and no position is ever rewritten. -/
theorem sched_output_prefix_safe {α : Type*} [DecidableEq α] (old new : List α) :
    old <+: safePublish old new := by
  unfold safePublish
  split
  · assumption
  · exact found_08_prefix_refl old

/-- Bounded-service core (Theorem L.14): with a positive fairness quantum, a continuously runnable
    wave accrues enough deficit credit to pay for a task of any cost after finitely many scheduler
    ticks, so it is not starved. -/
theorem sched_credit_reaches (cost quantum : ℕ) (hq : 0 < quantum) : ∃ n, cost ≤ n * quantum :=
  ⟨cost, Nat.le_mul_of_pos_right cost hq⟩

end CordialMiners
