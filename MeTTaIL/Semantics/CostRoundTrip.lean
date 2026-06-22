/-
Module: MeTTaIL.Semantics.CostRoundTrip
Layer: Semantics
Purpose: Abstract cost round trips for continued interactive GSLTs.
  The cost-accounting construction acts on continued interactive GSLTs, where every cut is presented
  as a wrapped, token-gated interaction. This file records the checked interface that the syntax-level
  cost endofunctor has to instantiate: starvation gives deadlock, wrapping is preserved by costed
  traces, and an idempotent round trip has an image equal to its fixed points up to bisimulation.
Imports: MeTTaIL.Semantics.Denotational
Trusted boundary: none
Main exports: Denotational.Costed.ContinuedCostSystem,
  Denotational.Costed.ContinuedCostSystem.starved_deadlocked,
  Denotational.Costed.ContinuedCostSystem.wrapped_trace_preserved,
  Denotational.Costed.CostRoundTrip, Denotational.Costed.CostRoundTrip.image_iff_fixed
Open obligations: instantiate `ContinuedCostSystem` for the generated cost presentation, then prove
  the concrete `T ∘ C` round trip is idempotent up to bisimulation for continued interactive GSLTs.
-/
import MeTTaIL.Semantics.Denotational

namespace MeTTaIL
namespace Denotational

namespace Costed

universe u v w x

/-- A state has no outgoing ordinary step. -/
def Deadlocked {State : Type u} {Label : Type v} (lts : LTS State Label) (s : State) : Prop :=
  ∀ t, ¬ Step lts s t

/-- A state has no outgoing costed step. -/
def CostDeadlocked {State : Type u} {Label : Type v} {Cost : Type w}
    (clts : CostedLTS State Label Cost) (s : State) : Prop :=
  ∀ t, ¬ CostedStep clts s t

/-- Costed deadlock is ordinary deadlock after forgetting costs. -/
theorem costDeadlocked_iff_forget_deadlocked {State : Type u} {Label : Type v} {Cost : Type w}
    (clts : CostedLTS State Label Cost) (s : State) :
    CostDeadlocked clts s ↔ Deadlocked clts.forget s := by
  constructor
  · intro h t hstep
    exact h t ((costedStep_forget clts).2 hstep)
  · intro h t hstep
    exact h t ((costedStep_forget clts).1 hstep)

/-- The abstract cost-accounted system supplied by a continued interactive GSLT instance. -/
structure ContinuedCostSystem (State : Type u) (Label : Type v) (Cost : Type w)
    (Signature : Type x) where
  costed : CostedLTS State Label Cost
  wrapped : State → Prop
  tokenAvailable : Signature → State → Prop
  token_of_step : ∀ {s label cost t}, costed.step s label cost t → ∃ sig, tokenAvailable sig s
  wrapped_of_step : ∀ {s label cost t}, costed.step s label cost t → wrapped s → wrapped t

namespace ContinuedCostSystem

/-- Starvation means that no gate token is available at the state. -/
def Starved {State : Type u} {Label : Type v} {Cost : Type w} {Signature : Type x}
    (S : ContinuedCostSystem State Label Cost Signature) (s : State) : Prop :=
  ∀ sig, ¬ S.tokenAvailable sig s

/-- A starved continued-cost state has no costed step. -/
theorem starved_costDeadlocked {State : Type u} {Label : Type v} {Cost : Type w}
    {Signature : Type x} (S : ContinuedCostSystem State Label Cost Signature) {s : State}
    (hstarved : S.Starved s) : CostDeadlocked S.costed s := by
  intro t hstep
  rcases hstep with ⟨label, cost, hcost⟩
  rcases S.token_of_step hcost with ⟨sig, htok⟩
  exact hstarved sig htok

/-- A starved continued-cost state is deadlocked after costs are forgotten. -/
theorem starved_deadlocked {State : Type u} {Label : Type v} {Cost : Type w}
    {Signature : Type x} (S : ContinuedCostSystem State Label Cost Signature) {s : State}
    (hstarved : S.Starved s) : Deadlocked S.costed.forget s :=
  (costDeadlocked_iff_forget_deadlocked S.costed s).1 (S.starved_costDeadlocked hstarved)

/-- Well-wrapping is preserved along every finite costed trace. -/
theorem wrapped_trace_preserved {State : Type u} {Label : Type v} {Cost : Type w}
    [Zero Cost] [Add Cost] {Signature : Type x}
    (S : ContinuedCostSystem State Label Cost Signature) {s t : State} {total : Cost}
    (htrace : Trace S.costed s total t) : S.wrapped s → S.wrapped t := by
  induction htrace with
  | refl s =>
      intro hwrap
      exact hwrap
  | tail label cost total hstep _ ih =>
      intro hwrap
      exact ih (S.wrapped_of_step hstep hwrap)

end ContinuedCostSystem

/-- An abstract round trip from a costed theory back into the original behavioural theory. -/
structure CostRoundTrip (State : Type u) (Label : Type v) where
  lts : LTS State Label
  roundTrip : State → State
  respects_bisim : ∀ {s t}, Bisimilar lts s t → Bisimilar lts (roundTrip s) (roundTrip t)
  idem : ∀ s, Bisimilar lts (roundTrip (roundTrip s)) (roundTrip s)

namespace CostRoundTrip

/-- The image of a round trip, read up to bisimulation. -/
def InImage {State : Type u} {Label : Type v} (R : CostRoundTrip State Label) (t : State) : Prop :=
  ∃ s, Bisimilar R.lts t (R.roundTrip s)

/-- A fixed point of the round trip, read up to bisimulation. -/
def Fixed {State : Type u} {Label : Type v} (R : CostRoundTrip State Label) (t : State) : Prop :=
  Bisimilar R.lts (R.roundTrip t) t

/-- Every image point is fixed when the round trip is idempotent up to bisimulation. -/
theorem image_subset_fixed {State : Type u} {Label : Type v}
    (R : CostRoundTrip State Label) {t : State} (h : R.InImage t) : R.Fixed t := by
  rcases h with ⟨s, hts⟩
  exact Bisimilar.trans (R.respects_bisim hts)
    (Bisimilar.trans (R.idem s) (Bisimilar.symm hts))

/-- Every fixed point belongs to the image, using itself as a representative. -/
theorem fixed_subset_image {State : Type u} {Label : Type v}
    (R : CostRoundTrip State Label) {t : State} (h : R.Fixed t) : R.InImage t :=
  ⟨t, Bisimilar.symm h⟩

/-- For an idempotent round trip, the image and the fixed points agree up to bisimulation. -/
theorem image_iff_fixed {State : Type u} {Label : Type v}
    (R : CostRoundTrip State Label) (t : State) :
    R.InImage t ↔ R.Fixed t :=
  ⟨R.image_subset_fixed, R.fixed_subset_image⟩

end CostRoundTrip

end Costed

end Denotational
end MeTTaIL
