-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: CordialMiners.Ref.WeightedCollector
Layer: Ref
Purpose: The executable weighted certificate collector and its connection to the Spec layer. The
  collector accepts valid distinct in-committee approvals, accumulates weight, and emits once the
  threshold is crossed. We prove the collector invariant (CERT-02), its preservation by every step
  (CERT-04), and soundness (CERT-03): an emitting state holds a threshold-heavy signer set.
Imports: CordialMiners.Spec.WeightedCertificate
Trusted boundary: human-reviewed spec / executable reference
Main exports: WCertState, collectorStep, WCertState.Inv, cert_02_init_inv, cert_04_step_inv,
  cert_03_collector_sound
Open obligations: CERT-08 collector completeness under fair delivery (conditional liveness, network
  boundary) is not in this module.
-/
import CordialMiners.Spec.WeightedCertificate

namespace CordialMiners

variable {P : Type*} [DecidableEq P]

/-- The collector state: the accepted signer set, the accumulated weight, and whether a certificate
    has been emitted. -/
structure WCertState (P : Type*) where
  signers : Finset P
  accWeight : Weight
  done : Bool

/-- The initial collector state. -/
def WCertState.init : WCertState P := ⟨∅, 0, false⟩

/-- One collector step on an incoming approval from `p`, whose validity is the abstract Boolean check
    `ok p`. Reject once done, off-committee, a duplicate signer, or invalid; otherwise accept `p`, add
    its weight, and emit once the threshold is crossed. One-shot and set-canonical. -/
def collectorStep (S : CommitteeSnapshot P) (ok : P → Bool) (st : WCertState P) (p : P) :
    WCertState P :=
  if st.done = true then st
  else if p ∈ S.committee ∧ p ∉ st.signers ∧ ok p = true then
    let w := st.accWeight + S.weight p
    ⟨insert p st.signers, w, thresholdPassedBool w S.totalWeight S.threshold⟩
  else st

/-- The collector invariant (CERT-02): the accumulated weight equals the weight of the accepted signer
    set, the signers are within the committee, and `done` implies the threshold was crossed. -/
def WCertState.Inv (S : CommitteeSnapshot P) (st : WCertState P) : Prop :=
  st.signers ⊆ S.committee ∧
  st.accWeight = wt S.weight st.signers ∧
  (st.done = true → thresholdPassed st.accWeight S.totalWeight S.threshold)

omit [DecidableEq P] in
/-- CERT-02 (base): the initial state satisfies the invariant. -/
theorem cert_02_init_inv (S : CommitteeSnapshot P) : (WCertState.init : WCertState P).Inv S := by
  refine ⟨by simp [WCertState.init], by simp [WCertState.init, wt], by simp [WCertState.init]⟩

/-- CERT-04: every collector step preserves the invariant. -/
theorem cert_04_step_inv (S : CommitteeSnapshot P) (ok : P → Bool) {st : WCertState P}
    (h : st.Inv S) (p : P) : (collectorStep S ok st p).Inv S := by
  obtain ⟨hsub, hacc, himp⟩ := h
  unfold collectorStep
  split
  · exact ⟨hsub, hacc, himp⟩
  · split
    · rename_i hguard
      obtain ⟨hpc, hpne, _⟩ := hguard
      refine ⟨Finset.insert_subset hpc hsub, ?_, ?_⟩
      · show st.accWeight + S.weight p = wt S.weight (insert p st.signers)
        rw [hacc]
        simp only [wt, Finset.sum_insert hpne]
        ring
      · intro hd
        exact (thresholdPassedBool_iff _ _ _).mp hd
    · exact ⟨hsub, hacc, himp⟩

omit [DecidableEq P] in
/-- CERT-03 (collector soundness): a state that has emitted holds a threshold-heavy signer set, so the
    emitted certificate is valid in the snapshot. -/
theorem cert_03_collector_sound (S : CommitteeSnapshot P) {st : WCertState P}
    (h : st.Inv S) (hd : st.done = true) : S.Heavy st.signers := by
  obtain ⟨hsub, hacc, himp⟩ := h
  exact ⟨hsub, hacc ▸ himp hd⟩

end CordialMiners
