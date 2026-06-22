/-
Module: MeTTaIL.Semantics.Denotational
Layer: Semantics
Purpose: The denotational-semantics interface suggested by the rset, rho, and knotted-topoi papers.
  The papers use the same abstract spine: a context-labelled transition system, a bisimulation over
  those labels, a denotation into a final behaviour object, and a full-abstraction theorem saying that
  equality of denotations is exactly bisimilarity. This file does not assert that the knotted-topos
  construction has been built in Lean. It gives the checked vocabulary and the small generic theorems
  needed to state that goal without overclaiming it.
Imports: MeTTaIL.Semantics.Eval
Trusted boundary: none
Main exports: LTS, IsSimulation, IsBisimulation, Bisimilar, KernelEq, FullyAbstract,
  FullyAbstractModel, RewriteLTS
Open obligations: instantiate this interface with the knotted-topos behaviour object, prove the
  MeTTaIL-to-rho operational correspondence on context labels, and calibrate context bisimulation
  against each object language's intended observational equivalence.
-/
import MeTTaIL.Semantics.Eval

namespace MeTTaIL
namespace Denotational

universe u v w z

/-- A labelled transition system. In the knotted-topoi account the labels are context labels. -/
structure LTS (State : Type u) (Label : Type v) where
  step : State → Label → State → Prop

/-- A forward simulation: each labelled move on the left is matched by a move with the same label. -/
def IsSimulation {State : Type u} {Label : Type v} (lts : LTS State Label)
    (R : State → State → Prop) : Prop :=
  ∀ {s t l s'}, R s t → lts.step s l s' → ∃ t', lts.step t l t' ∧ R s' t'

/-- A bisimulation is a symmetric simulation. The symmetry supplies the backward matching direction. -/
def IsBisimulation {State : Type u} {Label : Type v} (lts : LTS State Label)
    (R : State → State → Prop) : Prop :=
  (∀ {s t}, R s t → R t s) ∧ IsSimulation lts R

/-- Two states are bisimilar when some bisimulation relates them. -/
def Bisimilar {State : Type u} {Label : Type v} (lts : LTS State Label)
    (s t : State) : Prop :=
  ∃ R, IsBisimulation lts R ∧ R s t

namespace Bisimilar

/-- Bisimilarity is reflexive. Equality is a bisimulation. -/
theorem refl {State : Type u} {Label : Type v} (lts : LTS State Label) (s : State) :
    Bisimilar lts s s := by
  refine ⟨Eq, ?_, rfl⟩
  constructor
  · intro _ _ h
    exact h.symm
  · intro _ _ _ _ hEq hstep
    subst hEq
    exact ⟨_, hstep, rfl⟩

/-- Bisimilarity is symmetric by reading the witnessing bisimulation backwards. -/
theorem symm {State : Type u} {Label : Type v} {lts : LTS State Label} {s t : State}
    (h : Bisimilar lts s t) : Bisimilar lts t s := by
  rcases h with ⟨R, hR, hst⟩
  exact ⟨R, hR, hR.1 hst⟩

end Bisimilar

/-- The union of all bisimulations is itself a bisimulation. This is the coinductive reading of
    bisimilarity as the largest bisimulation. -/
theorem bisimilar_isBisimulation {State : Type u} {Label : Type v} (lts : LTS State Label) :
    IsBisimulation lts (Bisimilar lts) := by
  constructor
  · intro _ _ h
    exact Bisimilar.symm h
  · intro _ _ _ _ h hstep
    rcases h with ⟨R, hR, hst⟩
    rcases hR.2 hst hstep with ⟨t', ht', hRt'⟩
    exact ⟨t', ht', ⟨R, hR, hRt'⟩⟩

/-- The kernel relation of a denotation. -/
def KernelEq {State : Type u} {Den : Type w} (denote : State → Den) : State → State → Prop :=
  fun s t => denote s = denote t

/-- Full abstraction: denotational equality agrees exactly with bisimilarity. -/
def FullyAbstract {State : Type u} {Label : Type v} {Den : Type w}
    (lts : LTS State Label) (denote : State → Den) : Prop :=
  ∀ s t, KernelEq denote s t ↔ Bisimilar lts s t

/-- A kernel proof gives a full-abstraction theorem. This is the abstract shape used in the rho and
    knotted-topoi papers: equality in the behaviour object is the kernel of the final morphism, and that
    kernel is bisimilarity. -/
theorem fullyAbstract_of_kernel {State : Type u} {Label : Type v} {Den : Type w}
    (lts : LTS State Label) (denote : State → Den)
    (sound : ∀ {s t}, KernelEq denote s t → Bisimilar lts s t)
    (complete : ∀ {s t}, Bisimilar lts s t → KernelEq denote s t) :
    FullyAbstract lts denote := by
  intro s t
  exact ⟨sound, complete⟩

/-- A relation is a congruence for a chosen family of contexts when plugging related states into the
    same context preserves the relation. The knotted-topoi route needs this for context bisimilarity. -/
def Congruence {State : Type u} {Context : Type z} (plug : Context → State → State)
    (R : State → State → Prop) : Prop :=
  ∀ C {s t}, R s t → R (plug C s) (plug C t)

/-- The package a concrete denotational model must provide before LeaTTa can claim a fully abstract
    semantics for a language presentation. -/
structure FullyAbstractModel (State : Type u) (Label : Type v) (Den : Type w)
    (Context : Type z) where
  lts : LTS State Label
  denote : State → Den
  plug : Context → State → State
  full : FullyAbstract lts denote
  bisim_congruent : Congruence plug (Bisimilar lts)

namespace FullyAbstractModel

/-- The user-facing full-abstraction equation for a packaged model. -/
theorem eq_iff_bisimilar {State : Type u} {Label : Type v} {Den : Type w} {Context : Type z}
    (M : FullyAbstractModel State Label Den Context) (s t : State) :
    M.denote s = M.denote t ↔ Bisimilar M.lts s t :=
  M.full s t

/-- Denotational equality is sound for bisimilarity. -/
theorem bisimilar_of_eq {State : Type u} {Label : Type v} {Den : Type w} {Context : Type z}
    (M : FullyAbstractModel State Label Den Context) {s t : State}
    (h : M.denote s = M.denote t) : Bisimilar M.lts s t :=
  (M.full s t).1 h

/-- Bisimilarity is complete for denotational equality. -/
theorem eq_of_bisimilar {State : Type u} {Label : Type v} {Den : Type w} {Context : Type z}
    (M : FullyAbstractModel State Label Den Context) {s t : State}
    (h : Bisimilar M.lts s t) : M.denote s = M.denote t :=
  (M.full s t).2 h

end FullyAbstractModel

/-- The ordinary MeTTaIL rewrite relation as a one-label transition system. The knotted-topoi papers
    require a context-labelled system; this is the checked operational baseline that a future
    context-labelled system must refine or simulate. -/
def RewriteLTS (p : Presentation) : LTS AST Unit where
  step t _ t' := RewStep p t t'

/-- The current runtime's plain rewrite bisimilarity. The research target is a finer context-labelled
    version whose labels are minimal environments or term locations. -/
def RewriteBisimilar (p : Presentation) : AST → AST → Prop :=
  Bisimilar (RewriteLTS p)

/-- The executable evaluator always follows the checked rewrite relation, hence every finite run is a
    trace in the operational system that future denotational models must respect. -/
theorem eval_rewrite_trace (p : Presentation) (fuel : Nat) (t : AST) :
    RewStepMany p t (eval p fuel t) :=
  eval_sound p fuel t

end Denotational
end MeTTaIL
