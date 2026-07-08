-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: CordialMiners.Trec.Safety
Layer: Trec
Purpose: Causal well-formedness of the coarse theory. Every reachable coarse state respects the
  protocol's dependency chain: a quorum-approval rests on a proposal, a threshold certificate on a
  quorum-approval, a final on a certificate, and a final-leader on a final. Because the coarse state
  only grows (trec_step_monotone), a fact's precondition, once required, stays present. The composite
  result (trec_final_needs_propose) follows the whole chain from a final back to its proposal.
Imports: CordialMiners.Trec.Syntax
Trusted boundary: none (fully proved)
Main exports: TrecWF, trec_reachable_wf, trec_final_needs_propose
Open obligations: none
-/
import CordialMiners.Trec.Syntax

namespace CordialMiners

variable {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]

/-- Causal well-formedness: each derived fact has its immediate precondition fact present. This is the
    invariant the coarse step relation maintains, stated as a property of a single state. -/
def TrecWF (s : TrecState Wave Hash) : Prop :=
  (∀ w h, TrecFact.qApprove w h ∈ s → TrecFact.propose w h ∈ s) ∧
  (∀ w h, TrecFact.certThresh w h ∈ s → TrecFact.qApprove w h ∈ s) ∧
  (∀ w h, TrecFact.final w h ∈ s → TrecFact.certThresh w h ∈ s) ∧
  (∀ w h, TrecFact.finalLeader w h ∈ s → TrecFact.final w h ∈ s)

/-- Every state reachable from the empty state by coarse steps is causally well-formed. The empty
    state is vacuously well-formed; each step adds one fact whose precondition it required, and
    monotonicity keeps every earlier precondition in place. -/
theorem trec_reachable_wf {s : TrecState Wave Hash}
    (hreach : Relation.ReflTransGen TrecState.Step (∅ : TrecState Wave Hash) s) : TrecWF s := by
  induction hreach with
  | refl =>
    exact ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h,
           fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩
  | tail _ hstep ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih
    cases hstep <;>
      refine ⟨fun w h hm => ?_, fun w h hm => ?_, fun w h hm => ?_, fun w h hm => ?_⟩ <;>
      aesop

/-- The full causal chain: in any reachable coarse state, a final fact is backed by the proposal it
    descends from. Two correct miners that both see `final w h` therefore agree it began as the same
    proposal, which is the coarse mirror of threshold-finality safety. -/
theorem trec_final_needs_propose {s : TrecState Wave Hash}
    (hreach : Relation.ReflTransGen TrecState.Step (∅ : TrecState Wave Hash) s)
    {w : Wave} {h : Hash} (hfin : TrecFact.final w h ∈ s) : TrecFact.propose w h ∈ s := by
  obtain ⟨i1, i2, i3, _⟩ := trec_reachable_wf hreach
  exact i1 w h (i2 w h (i3 w h hfin))

end CordialMiners
