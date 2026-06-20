/-
Module: CordialMiners.Proofs.EndToEndSafety
Layer: Proofs
Purpose: The top-level safety statement (the blueprint's Theorem 4.54 core). It composes the verified
  component results into one guarantee: under snapshot well-formedness, the Byzantine-weight bound, and
  honest non-equivocation, PoR-weighted Cordial Miners is safe. cm_threshold_agreement is the positive
  Byzantine-agreement form of CERT-06 (all valid certificates carry the same value). cm_end_to_end_safety
  bundles leader-agreement (FL-07), output consistency (TAU-09), and blocklace integrity (BL-02).
  cm_concrete_ordering_valid certifies that the concrete deterministic ordering is a dup-free topological
  enumeration of exactly its input, so the deterministic-ordering obligation is discharged by a real
  algorithm.
Imports: CordialMiners.Spec.FinalLeader, CordialMiners.Spec.TauOrderSpec, CordialMiners.Ref.TauOrder
Trusted boundary: none (fully proved; rests only on the human-reviewed specs it composes)
Main exports: cm_threshold_agreement, cm_end_to_end_safety, cm_concrete_ordering_valid
Open obligations: prefix-monotonicity under leader safety (OutputMonotone, the TAU-08 leader-safety
  package) enters cm_end_to_end_safety as an explicit hypothesis, matching the blueprint's trusted
  boundary; liveness (dissemination completeness, scheduler non-starvation) is conditional on the
  network and scheduler fairness assumptions stated in the dissemination and scheduler specs.
-/
import CordialMiners.Spec.FinalLeader
import CordialMiners.Spec.TauOrderSpec
import CordialMiners.Ref.TauOrder

namespace CordialMiners

/-- Byzantine agreement, the positive form of CERT-06: under honest non-equivocation and the
    Byzantine-weight bound, every pair of valid threshold certificates for a snapshot carries the same
    value. There is no fork at the certificate level. -/
theorem cm_threshold_agreement {P V : Type*} [DecidableEq P]
    (S : CommitteeSnapshot P) (hWF : S.WF) (approved : P → V → Prop) (honest : Finset P)
    (hNoEquiv : ∀ p ∈ honest, ∀ v v' : V, approved p v → approved p v' → v = v')
    (hByz : S.ByzBound honest)
    {c c' : ThresholdCert P V} (hc : ValidCert S approved c) (hc' : ValidCert S approved c') :
    c.value = c'.value := by
  by_contra hne
  exact cert_06_no_conflicting_threshold_finals S hWF approved honest hNoEquiv hByz hc hc' hne

/-- End-to-end safety (Theorem 4.54 core). Under the standard assumptions the protocol guarantees, in
    one statement:
    (1) leader-agreement: no two valid ratification certificates ratify conflicting target blocks;
    (2) output consistency: correct miners whose blocklaces sit inside a common limit produce
        prefix-comparable orders, so they never publish a conflicting position;
    (3) blocklace integrity: dissemination's receive-path preserves parent closure.
    The ordering's prefix-monotonicity (leader safety) enters as the hypothesis `hmono`, matching the
    blueprint's leader-safety trusted boundary. -/
theorem cm_end_to_end_safety {P Wave Slot Hash : Type*}
    [DecidableEq P] [DecidableEq Wave] [DecidableEq Slot] [DecidableEq Hash]
    (S : CommitteeSnapshot P) (hWF : S.WF) (L : Blocklace P Wave Slot Hash) (honest : Finset P)
    (hByz : S.ByzBound honest)
    (hNoEquiv : ∀ p ∈ honest, ∀ b b' : Block P Wave Slot Hash,
      BlockApproves L p b → BlockApproves L p b' → b = b')
    (tau : Ordering P Wave Slot Hash) (hmono : OutputMonotone tau) :
    (∀ {rc rc' : ThresholdCert P (Block P Wave Slot Hash)},
        ValidRatCert S L rc → ValidRatCert S L rc' → ¬ ConflictBlock rc.value rc'.value)
    ∧ (∀ {L₁ L₂ Limit : Blocklace P Wave Slot Hash},
        L₁ ⊆ Limit → L₂ ⊆ Limit → tau L₁ <+: tau L₂ ∨ tau L₂ <+: tau L₁)
    ∧ (∀ {L' : Blocklace P Wave Slot Hash} {b : Block P Wave Slot Hash},
        ParentClosed L' → b.parents ⊆ hashesOf L' → ParentClosed (insert b L')) := by
  refine ⟨fun hrc hrc' hconf => ?_, fun h₁ h₂ => ?_, fun hL hb => ?_⟩
  · exact fl_07_no_conflicting_ratifications S hWF L honest hNoEquiv hByz hrc hrc' hconf
  · exact tau_09_output_consistent hmono h₁ h₂
  · exact bl_02_insert_parentClosed hL hb

/-- The concrete deterministic ordering is a valid total order of its input: it is duplicate-free,
    topologically sorted (no dependency after its dependent), and (under the strict-rank acyclicity
    hypothesis) enumerates exactly the input vertices. With determinism (topoSort is a function), the
    deterministic-ordering requirement is met by a real, computable algorithm. -/
theorem cm_concrete_ordering_valid {H : Type*} [LinearOrder H] (V : Finset H) (deps : H → Finset H)
    {rank : H → ℕ} (hrank : ∀ x, ∀ p ∈ deps x, rank p < rank x) :
    (topoSort V deps).Nodup
    ∧ TopoSorted deps (topoSort V deps)
    ∧ (∀ y, y ∈ topoSort V deps ↔ y ∈ V) :=
  ⟨topoSort_nodup V deps, topoSort_topoSorted V deps,
   fun _ => ⟨fun hy => topoSort_subset V deps hy, fun hy => topoSort_complete V deps hrank hy⟩⟩

end CordialMiners
