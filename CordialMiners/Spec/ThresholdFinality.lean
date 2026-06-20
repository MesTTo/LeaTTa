/-
Module: CordialMiners.Spec.ThresholdFinality
Layer: Spec
Purpose: Self-enforcing threshold finality. The crown-jewel safety theorem CERT-06: under the
  Byzantine-weight bound and honest non-equivocation, two valid threshold certificates cannot carry
  conflicting values. This is where the weighted-overlap lemma pays off: the overlap of two heavy
  signer sets is heavier than the adversary bound, so it must contain an honest signer, who would then
  have approved both conflicting values.
Imports: CordialMiners.Spec.WeightedCertificate
Trusted boundary: human-reviewed spec
Main exports: cert_06_no_conflicting_threshold_finals
Open obligations: none
-/
import CordialMiners.Spec.WeightedCertificate

namespace CordialMiners

variable {P V : Type*} [DecidableEq P]

/-- A plain-natural arithmetic step, factored out so the proof stays clear of product atoms. -/
private theorem sub_lt_of {a b c d : ℕ} (h1 : a + b ≤ c) (h2 : c < d + b) : a < d := by omega

/-- CERT-06 (no conflicting threshold finals). Under honest non-equivocation and the Byzantine-weight
    bound `S.ByzBound honest`, two valid threshold certificates for the same snapshot cannot carry
    conflicting (distinct) values. Threshold finality is therefore self-enforcing: it needs no health
    assumption, only the adversary bound and that honest members do not sign two values. -/
theorem cert_06_no_conflicting_threshold_finals
    (S : CommitteeSnapshot P) (hWF : S.WF)
    (approved : P → V → Prop) (honest : Finset P)
    (hNoEquiv : ∀ p ∈ honest, ∀ v v' : V, approved p v → approved p v' → v = v')
    (hByz : S.ByzBound honest)
    {c c' : ThresholdCert P V}
    (hc : ValidCert S approved c) (hc' : ValidCert S approved c')
    (hconf : c.value ≠ c'.value) : False := by
  obtain ⟨hAh, hAappr⟩ := hc
  obtain ⟨hBh, hBappr⟩ := hc'
  -- The overlap of the two heavy signer sets is heavier than the Byzantine bound.
  have hover := cert_05_heavy_overlap S hWF hAh hBh
  have hwlt : wt S.weight (S.committee \ honest) < wt S.weight (c.signers ∩ c'.signers) := by
    have h1 : wt S.weight (S.committee \ honest) * S.threshold.den
              < wt S.weight (c.signers ∩ c'.signers) * S.threshold.den :=
      sub_lt_of hByz hover
    exact lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
  -- So the overlap cannot lie entirely in the non-honest set: it contains an honest signer.
  have hne : (c.signers ∩ c'.signers ∩ honest).Nonempty := by
    rcases (c.signers ∩ c'.signers ∩ honest).eq_empty_or_nonempty with hemp | hne
    · exfalso
      have hsub : c.signers ∩ c'.signers ⊆ S.committee \ honest := by
        intro p hp
        have hpcomm : p ∈ S.committee := hAh.1 (Finset.mem_of_mem_inter_left hp)
        rw [Finset.mem_sdiff]
        refine ⟨hpcomm, fun hph => ?_⟩
        have hmem : p ∈ c.signers ∩ c'.signers ∩ honest := Finset.mem_inter.mpr ⟨hp, hph⟩
        rw [hemp] at hmem
        simp at hmem
      have hmono := found_03_weight_mono S.weight hsub
      exact absurd (lt_of_le_of_lt hmono hwlt) (lt_irrefl _)
    · exact hne
  -- That honest signer approved both values, so the values are equal, contradicting the conflict.
  obtain ⟨p, hp⟩ := hne
  rw [Finset.mem_inter, Finset.mem_inter] at hp
  obtain ⟨⟨hpA, hpB⟩, hpH⟩ := hp
  exact hconf (hNoEquiv p hpH c.value c'.value (hAappr p hpA) (hBappr p hpB))

end CordialMiners
