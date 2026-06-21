/-
Module: CordialMiners.Proofs.EndToEndSafety
Layer: Proofs
Purpose: The top-level safety statement (the blueprint's Theorem 4.54 core). It composes the verified
  component results into one guarantee: under snapshot well-formedness, the Byzantine-weight bound, and
  honest non-equivocation, PoR-weighted Cordial Miners is safe. threshold_certificates_agree is the
  positive Byzantine-agreement form of CERT-06: all valid certificates carry the same value.
  end_to_end_safety_of_output_monotone bundles leader-agreement (FL-07), output consistency (TAU-09),
  and blocklace integrity (BL-02) as EndToEndSafety. topoSort_valid certifies that the concrete
  deterministic ordering is a dup-free topological enumeration of exactly its input, so the
  deterministic-ordering obligation is discharged by a real algorithm.
Imports: CordialMiners.Spec.FinalLeader, CordialMiners.Spec.TauOrderSpec, CordialMiners.Ref.TauOrder
Trusted boundary: none (fully proved; rests only on the human-reviewed specs it composes)
Main exports: EndToEndSafety, EndToEndAssumptions, threshold_certificates_agree,
  end_to_end_safety_of_output_monotone, end_to_end_safety_of_anchor_prefix_monotone,
  end_to_end_safety_of_finalized_count_monotone, end_to_end_safety_of_finality_permanence,
  topoSort_valid
Open obligations: the ordering hypothesis is discharged in stages.
  end_to_end_safety_of_output_monotone takes abstract OutputMonotone;
  end_to_end_safety_of_anchor_prefix_monotone derives it from AnchorPrefixMonotone (TAU-08);
  end_to_end_safety_of_finalized_count_monotone derives that from the scalar fact that the finalized-wave
  count is monotone; end_to_end_safety_of_finality_permanence derives even that from finality permanence
  (a finalized wave stays finalized as the blocklace grows). The safety story then rests on three named
  facts: the Byzantine-weight bound, honest non-equivocation, and finality permanence. Liveness
  (dissemination completeness, scheduler non-starvation) is conditional on the network and scheduler
  fairness assumptions stated in the dissemination and scheduler specs.
-/
import CordialMiners.Spec.FinalLeader
import CordialMiners.Spec.TauOrderSpec
import CordialMiners.Ref.TauOrder
import CordialMiners.Ref.AnchoredOrder
import CordialMiners.Ref.FinalizedAnchors
import CordialMiners.Ref.FinalityPermanence

namespace CordialMiners

/-- Byzantine agreement, the positive form of CERT-06: under honest non-equivocation and the
    Byzantine-weight bound, every pair of valid threshold certificates for a snapshot carries the same
    value. There is no fork at the certificate level. -/
theorem threshold_certificates_agree {P V : Type*} [DecidableEq P]
    (S : CommitteeSnapshot P) (hWF : S.WF) (approved : P → V → Prop) (honest : Finset P)
    (hNoEquiv : ∀ p ∈ honest, ∀ v v' : V, approved p v → approved p v' → v = v')
    (hByz : S.ByzBound honest)
    {c c' : ThresholdCert P V} (hc : ValidCert S approved c) (hc' : ValidCert S approved c') :
    c.value = c'.value := by
  by_contra hne
  exact cert_06_no_conflicting_threshold_finals S hWF approved honest hNoEquiv hByz hc hc' hne

section EndToEnd

variable {P Wave Slot Hash : Type*}
variable [DecidableEq P] [DecidableEq Wave] [DecidableEq Slot] [DecidableEq Hash]

/-- The shared end-to-end safety conclusion: no conflicting leader ratifications, prefix-comparable
    outputs below a common limit, and parent closure preserved by receive-path insertion. -/
def EndToEndSafety (S : CommitteeSnapshot P) (L : Blocklace P Wave Slot Hash)
    (tau : Ordering P Wave Slot Hash) : Prop :=
  (∀ {rc rc' : ThresholdCert P (Block P Wave Slot Hash)},
      ValidRatCert S L rc → ValidRatCert S L rc' → ¬ ConflictBlock rc.value rc'.value)
  ∧ (∀ {L₁ L₂ Limit : Blocklace P Wave Slot Hash},
      L₁ ⊆ Limit → L₂ ⊆ Limit → tau L₁ <+: tau L₂ ∨ tau L₂ <+: tau L₁)
  ∧ (∀ {L' : Blocklace P Wave Slot Hash} {b : Block P Wave Slot Hash},
      ParentClosed L' → b.parents ⊆ hashesOf L' → ParentClosed (insert b L'))

/-- The assumptions shared by the end-to-end safety variants. The ordering-specific assumption is kept
    separate, since each theorem discharges it from a different source. -/
structure EndToEndAssumptions (S : CommitteeSnapshot P) (L : Blocklace P Wave Slot Hash)
    (honest : Finset P) : Prop where
  wf : S.WF
  byz_bound : S.ByzBound honest
  honest_non_equivocation :
    ∀ p ∈ honest, ∀ b b' : Block P Wave Slot Hash,
      BlockApproves L p b → BlockApproves L p b' → b = b'

/-- End-to-end safety (Theorem 4.54 core). Under the standard assumptions the protocol guarantees, in
    one statement:
    (1) leader-agreement: no two valid ratification certificates ratify conflicting target blocks;
    (2) output consistency: correct miners whose blocklaces sit inside a common limit produce
        prefix-comparable orders, so they never publish a conflicting position;
    (3) blocklace integrity: dissemination's receive-path preserves parent closure.
    The ordering's prefix-monotonicity (leader safety) enters as the hypothesis `hmono`, matching the
    blueprint's leader-safety trusted boundary. -/
theorem end_to_end_safety_of_output_monotone
    (S : CommitteeSnapshot P) (L : Blocklace P Wave Slot Hash) (honest : Finset P)
    (h : EndToEndAssumptions S L honest)
    (tau : Ordering P Wave Slot Hash) (hmono : OutputMonotone tau) :
    EndToEndSafety S L tau := by
  refine ⟨fun hrc hrc' hconf => ?_, fun h₁ h₂ => ?_, fun hL hb => ?_⟩
  · exact fl_07_no_conflicting_ratifications S h.wf L honest h.honest_non_equivocation h.byz_bound
      hrc hrc' hconf
  · exact tau_09_output_consistent hmono h₁ h₂
  · exact bl_02_insert_parentClosed hL hb

/-- The concrete deterministic ordering is a valid total order of its input: it is duplicate-free,
    topologically sorted (no dependency after its dependent), and (under the strict-rank acyclicity
    hypothesis) enumerates exactly the input vertices. With determinism (topoSort is a function), the
    deterministic-ordering requirement is met by a real, computable algorithm. -/
theorem topoSort_valid {H : Type*} [LinearOrder H] (V : Finset H) (deps : H → Finset H)
    {rank : H → ℕ} (hrank : ∀ x, ∀ p ∈ deps x, rank p < rank x) :
    (topoSort V deps).Nodup
    ∧ TopoSorted deps (topoSort V deps)
    ∧ (∀ y, y ∈ topoSort V deps ↔ y ∈ V) :=
  ⟨topoSort_nodup V deps, topoSort_topoSorted V deps,
   fun _ => ⟨fun hy => topoSort_subset V deps hy, fun hy => topoSort_complete V deps hrank hy⟩⟩

/-- End-to-end safety with the ordering hypothesis discharged. Same guarantee as
    end_to_end_safety_of_output_monotone,
    but for the concrete anchored ordering and assuming only the primitive leader-safety fact: the
    finalized-anchor sequence is prefix-monotone in the blocklace. Output-prefix monotonicity (TAU-08)
    is now derived (tau_08_anchored_output_monotone), not assumed, so the only ordering input is
    AnchorPrefixMonotone, which is much closer to the protocol than abstract OutputMonotone. -/
theorem end_to_end_safety_of_anchor_prefix_monotone
    (S : CommitteeSnapshot P) (L : Blocklace P Wave Slot Hash) (honest : Finset P)
    (h : EndToEndAssumptions S L honest)
    (anchors : Blocklace P Wave Slot Hash → List Hash) (hist : Hash → List Hash)
    (hLead : AnchorPrefixMonotone anchors) :
    EndToEndSafety S L (anchoredOrder anchors hist) :=
  end_to_end_safety_of_output_monotone S L honest h (anchoredOrder anchors hist)
    (tau_08_anchored_output_monotone anchors hist hLead)

/-- The deepest form: end-to-end safety with a fully concrete ordering and the ordering hypothesis
    reduced to one scalar fact. The ordering is the anchored order over the finalized-anchor sequence,
    and the only ordering input is that the finalized-wave count `finalCount` is monotone in the
    blocklace (finality permanence plus wave-ordered finalization). Anchor prefix-monotonicity and
    output-prefix monotonicity are both derived. -/
theorem end_to_end_safety_of_finalized_count_monotone
    (S : CommitteeSnapshot P) (L : Blocklace P Wave Slot Hash) (honest : Finset P)
    (h : EndToEndAssumptions S L honest)
    (finalCount : Blocklace P Wave Slot Hash → ℕ) (leaderOf : ℕ → Hash) (hist : Hash → List Hash)
    (hCount : ∀ {L₁ L₂ : Blocklace P Wave Slot Hash}, L₁ ⊆ L₂ → finalCount L₁ ≤ finalCount L₂) :
    EndToEndSafety S L (anchoredOrder (finalizedAnchors finalCount leaderOf) hist) :=
  end_to_end_safety_of_anchor_prefix_monotone S L honest h
    (finalizedAnchors finalCount leaderOf) hist
    (finalizedAnchors_prefixMonotone finalCount leaderOf hCount)

/-- The final form: PoR-weighted Cordial Miners is safe, resting on three named facts. Given the
    Byzantine-weight bound (hByz), honest non-equivocation (hNoEquiv), and finality permanence (hperm:
    a finalized wave stays finalized as the blocklace grows), the protocol guarantees leader-agreement,
    output consistency, and blocklace integrity, for the fully concrete finalized-anchor ordering. The
    bound monotonicity (hbound) is a technical artifact satisfied by the block count. Every other
    ordering property (the finalized-wave count's monotonicity, anchor prefix-monotonicity, and
    output-prefix monotonicity) is derived. -/
theorem end_to_end_safety_of_finality_permanence
    (S : CommitteeSnapshot P) (L : Blocklace P Wave Slot Hash) (honest : Finset P)
    (h : EndToEndAssumptions S L honest)
    (Final : Blocklace P Wave Slot Hash → ℕ → Prop) [∀ L w, Decidable (Final L w)]
    (bound : Blocklace P Wave Slot Hash → ℕ) (leaderOf : ℕ → Hash) (hist : Hash → List Hash)
    (hperm : ∀ (w : ℕ) {L₁ L₂ : Blocklace P Wave Slot Hash}, L₁ ⊆ L₂ → Final L₁ w → Final L₂ w)
    (hbound : ∀ {L₁ L₂ : Blocklace P Wave Slot Hash}, L₁ ⊆ L₂ → bound L₁ ≤ bound L₂) :
    EndToEndSafety S L (anchoredOrder (finalizedAnchors (finalCountOf Final bound) leaderOf) hist) :=
  end_to_end_safety_of_finalized_count_monotone S L honest h
    (finalCountOf Final bound) leaderOf hist
    (finalCountOf_monotone Final bound hperm hbound)

end EndToEnd

end CordialMiners
