/-
Module: CordialMiners.Spec.TauOrderSpec
Layer: Spec
Purpose: The abstract contract of the deterministic ordering function tau_ord and its output-prefix
  discipline (IC10). The ordering is a pure function (so deterministic), and under leader safety it is
  prefix-monotone in the blocklace. The headline safety result here is output consistency (TAU-09): two
  correct miners whose blocklaces are sub-blocklaces of a common limit produce prefix-comparable
  outputs, so they never publish conflicting positions. Proven from the prefix theory FOUND-08.
Imports: CordialMiners.Foundation.Prefix, CordialMiners.Spec.Blocklace
Trusted boundary: human-reviewed spec
Main exports: Ordering, OutputMonotone, tau_04_deterministic, tau_10_publish_extends,
  tau_09_output_consistent
Open obligations: the concrete tau_ord algorithm (canonical topological sort + anchor recursion, with
  its cache correctness TAU-07 and the proof of OutputMonotone under leader safety TAU-08) is the
  Ref.TauOrder work, built from Appendix J.
-/
import CordialMiners.Foundation.Prefix
import CordialMiners.Spec.Blocklace

namespace CordialMiners

variable {P Wave Slot Hash : Type*}

/-- An ordering function turns a blocklace into the published ordered prefix of block hashes. -/
abbrev Ordering (P Wave Slot Hash : Type*) := Blocklace P Wave Slot Hash → List Hash

/-- TAU-04 (determinism): an ordering is a pure function, so equal blocklaces give equal outputs. The
    concrete tau_ord achieves this by canonical tie-breaking at every maximum, sort, and selection. -/
theorem tau_04_deterministic (tau : Ordering P Wave Slot Hash) {L₁ L₂ : Blocklace P Wave Slot Hash}
    (h : L₁ = L₂) : tau L₁ = tau L₂ := by rw [h]

/-- TAU-08 contract: the ordering is prefix-monotone in the blocklace. Growing the blocklace only
    extends the ordered output (this is what leader safety buys for the concrete algorithm). -/
def OutputMonotone (tau : Ordering P Wave Slot Hash) : Prop :=
  ∀ {L₁ L₂ : Blocklace P Wave Slot Hash}, L₁ ⊆ L₂ → tau L₁ <+: tau L₂

/-- TAU-10 / IC10 (output-prefix discipline): a prefix-monotone ordering publishes only prefix
    extensions, so a later, larger blocklace's output extends the earlier one. -/
theorem tau_10_publish_extends {tau : Ordering P Wave Slot Hash} (hmono : OutputMonotone tau)
    {L₁ L₂ : Blocklace P Wave Slot Hash} (h : L₁ ⊆ L₂) : tau L₁ <+: tau L₂ := hmono h

/-- TAU-09 (output consistency): if two blocklaces are each a sub-blocklace of a common limit and the
    ordering is prefix-monotone, the two orderings are prefix-comparable. Two correct miners whose
    local blocklaces sit inside one limit blocklace therefore never disagree on a published position,
    one output is always a prefix of the other. -/
theorem tau_09_output_consistent {tau : Ordering P Wave Slot Hash} (hmono : OutputMonotone tau)
    {L₁ L₂ Limit : Blocklace P Wave Slot Hash} (h₁ : L₁ ⊆ Limit) (h₂ : L₂ ⊆ Limit) :
    tau L₁ <+: tau L₂ ∨ tau L₂ <+: tau L₁ :=
  found_08_prefix_comparable (hmono h₁) (hmono h₂)

end CordialMiners
