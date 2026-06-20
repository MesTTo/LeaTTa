/-
Module: CordialMiners.Ref.AnchoredOrder
Layer: Ref
Purpose: Discharge the ordering's prefix-monotonicity (TAU-08) to a cleaner, more primitive leader-safety
  fact. The real ordering is anchored: it concatenates, in finalized-leader order, each anchor's committed
  causal history. An anchor's committed history is fixed once the anchor is finalized (finality is
  permanent), so the only way the blocklace can change the output is by extending the anchor sequence.
  We model this as anchoredOrder = (anchors L).flatMap hist and prove: if the anchor sequence is
  prefix-monotone in the blocklace (AnchorPrefixMonotone, the isolated leader-safety fact), then the
  anchored ordering is output-monotone. OutputMonotone is therefore a theorem here, not an assumption.
Imports: CordialMiners.Spec.TauOrderSpec
Trusted boundary: none (fully proved). AnchorPrefixMonotone is the leader-safety hypothesis the protocol
  supplies; this module derives the whole output-prefix discipline from it.
Main exports: anchoredOrder, AnchorPrefixMonotone, tau_08_anchored_output_monotone
Open obligations: deriving AnchorPrefixMonotone itself from finality permanence and wave-ordered
  finalization is the deeper leader-safety package.
-/
import CordialMiners.Spec.TauOrderSpec

namespace CordialMiners

variable {P Wave Slot Hash : Type*}

/-- The anchored ordering: concatenate, in finalized-leader order, each anchor's committed causal
    history. `anchors L` is the sequence of finalized leader hashes; `hist a` is the canonical ordered
    committed history below anchor `a`, which is fixed once `a` is finalized. -/
def anchoredOrder (anchors : Blocklace P Wave Slot Hash → List Hash) (hist : Hash → List Hash) :
    Ordering P Wave Slot Hash := fun L => (anchors L).flatMap hist

/-- Leader safety, isolated: as the blocklace grows, the finalized-anchor sequence extends as a prefix.
    Finalized leaders are permanent and ordered by wave, so newly finalized leaders append after the
    existing ones rather than reordering them. -/
def AnchorPrefixMonotone (anchors : Blocklace P Wave Slot Hash → List Hash) : Prop :=
  ∀ {L₁ L₂ : Blocklace P Wave Slot Hash}, L₁ ⊆ L₂ → anchors L₁ <+: anchors L₂

/-- TAU-08 discharged: when the anchor sequence is prefix-monotone (leader safety), the anchored
    ordering is output-monotone. Each anchor's committed history is fixed, so extending the anchor
    sequence only appends more blocks to the output, never reorders the published prefix. -/
theorem tau_08_anchored_output_monotone
    (anchors : Blocklace P Wave Slot Hash → List Hash) (hist : Hash → List Hash)
    (hmono : AnchorPrefixMonotone anchors) :
    OutputMonotone (anchoredOrder anchors hist) := by
  intro L₁ L₂ hsub
  obtain ⟨rest, hrest⟩ := hmono hsub
  show (anchors L₁).flatMap hist <+: (anchors L₂).flatMap hist
  rw [← hrest, List.flatMap_append]
  exact List.prefix_append _ _

end CordialMiners
