/-
Module: CordialMiners.Spec.WeightedCertificate
Layer: Spec
Purpose: Weighted threshold certificates and their validity, plus the certificate-level overlap lemma
  CERT-05 (two threshold-heavy signer sets overlap beyond the adversary bound), the restatement of the
  foundational weighted-overlap lemma for snapshots.
Imports: CordialMiners.Spec.Snapshot
Trusted boundary: human-reviewed spec
Main exports: ThresholdCert, ValidCert, cert_05_heavy_overlap
Open obligations: none
-/
import CordialMiners.Spec.Snapshot

namespace CordialMiners

variable {P V : Type*} [DecidableEq P]

/-- A weighted threshold certificate for a candidate value: the value and the set of signers. The
    cryptographic evidence (one approval signature per signer) is abstracted into the `approved`
    predicate of `ValidCert`; the weight argument is what the safety proof turns on. -/
structure ThresholdCert (P V : Type*) where
  value : V
  signers : Finset P

/-- A certificate is valid for a snapshot and an approval relation when its signer set is
    threshold-heavy and every signer approved the certificate's value. -/
def ValidCert (S : CommitteeSnapshot P) (approved : P → V → Prop) (c : ThresholdCert P V) : Prop :=
  S.Heavy c.signers ∧ ∀ p ∈ c.signers, approved p c.value

/-- CERT-05: two threshold-heavy signer sets overlap beyond `(2θ − 1)W` of the committee weight. The
    snapshot-level restatement of `FOUND-05`, the basis of no-conflicting-finals. -/
theorem cert_05_heavy_overlap (S : CommitteeSnapshot P) (hWF : S.WF) {A B : Finset P}
    (hA : S.Heavy A) (hB : S.Heavy B) :
    2 * (S.threshold.num * S.totalWeight)
      < wt S.weight (A ∩ B) * S.threshold.den + S.totalWeight * S.threshold.den := by
  obtain ⟨hAsub, hAh⟩ := hA
  obtain ⟨hBsub, hBh⟩ := hB
  have hWeq := hWF.1
  rw [hWeq] at hAh hBh ⊢
  exact found_05_weighted_overlap S.weight S.threshold hAsub hBsub hAh hBh

end CordialMiners
