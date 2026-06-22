/-
Module: MeTTaIL.Semantics.Denotational
Layer: Semantics
Purpose: The denotational-semantics interface suggested by the rset, rho, path-subspace, and
  knotted-topoi papers.
  The papers use the same abstract spine: a context-labelled transition system, a bisimulation over
  those labels, a denotation into a final behaviour object, and a full-abstraction theorem saying that
  equality of denotations is exactly bisimilarity. The module does not assert that the knotted-topos
  construction has been built in Lean. The module gives the checked vocabulary and generic theorems
  needed to state that goal without overclaiming it.
Imports: MeTTaIL.Semantics.Eval, Mathlib.Logic.Relation
Trusted boundary: none
Main exports: LTS, IsSimulation, IsBisimulation, Bisimilar, KernelEq, FullyAbstract,
  BisimilarityPreserving, BisimilarityReflecting, FullyAbstractModel, PathRSpace, CostedLTS, RewriteLTS
Open obligations: instantiate this interface with the knotted-topos behaviour object, prove the
  MeTTaIL-to-rho operational correspondence on context labels, and calibrate context bisimulation
  against each object language's intended observational equivalence. For path-key RSpace, also prove the
  trie store, cut distributive law, and subspace reaction confluence promised by the path-subspace paper.
  For cost-accounted GSLTs, instantiate the costed transition layer with phlogiston tokens, wrapped
  continuations, and resource-sufficiency proofs.
-/
import MeTTaIL.Semantics.Eval
import Mathlib.Logic.Relation

namespace MeTTaIL
namespace Denotational

universe u v w x y z q

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

/-- The union of all bisimulations is itself a bisimulation. The theorem gives the coinductive reading of
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

/-- A kernel proof gives a full-abstraction theorem. The theorem is the abstract argument used in the rho and
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

/-- A translation preserves bisimilarity when source-equivalent states translate to target-equivalent
    states. For the MeTTaIL-to-rho route, this is one half of operational correspondence. -/
def BisimilarityPreserving {SrcState : Type u} {SrcLabel : Type v} {TgtState : Type x}
    {TgtLabel : Type y} (src : LTS SrcState SrcLabel) (tgt : LTS TgtState TgtLabel)
    (translate : SrcState → TgtState) : Prop :=
  ∀ {s t}, Bisimilar src s t → Bisimilar tgt (translate s) (translate t)

/-- A translation reflects bisimilarity when target-equivalent translations came from source-equivalent
    states. Reflection prevents the denotation from identifying too many source states. -/
def BisimilarityReflecting {SrcState : Type u} {SrcLabel : Type v} {TgtState : Type x}
    {TgtLabel : Type y} (src : LTS SrcState SrcLabel) (tgt : LTS TgtState TgtLabel)
    (translate : SrcState → TgtState) : Prop :=
  ∀ {s t}, Bisimilar tgt (translate s) (translate t) → Bisimilar src s t

/-- Full abstraction transfers back along a translation that preserves and reflects bisimilarity. After a
    MeTTaIL presentation is translated to a target calculus such as rho, this theorem pulls the target
    denotation back to the source. -/
theorem fullyAbstract_of_bisimilarity_translation {SrcState : Type u} {SrcLabel : Type v}
    {TgtState : Type x} {TgtLabel : Type y} {Den : Type w} (src : LTS SrcState SrcLabel)
    (tgt : LTS TgtState TgtLabel) (denote : TgtState → Den) (translate : SrcState → TgtState)
    (hfull : FullyAbstract tgt denote)
    (hpres : BisimilarityPreserving src tgt translate)
    (hreflect : BisimilarityReflecting src tgt translate) :
    FullyAbstract src (fun s => denote (translate s)) := by
  intro s t
  constructor
  · intro hden
    exact hreflect ((hfull (translate s) (translate t)).1 hden)
  · intro hbis
    exact (hfull (translate s) (translate t)).2 (hpres hbis)

/-- Context congruence transfers back along a translation when source plugging commutes with target
    plugging up to the translation. A MeTTaIL-to-rho desugaring has to supply this commuting square. -/
theorem congruence_of_bisimilarity_translation {SrcState : Type u} {SrcLabel : Type v}
    {SrcContext : Type z} {TgtState : Type x} {TgtLabel : Type y} {TgtContext : Type q}
    (src : LTS SrcState SrcLabel) (tgt : LTS TgtState TgtLabel)
    (srcPlug : SrcContext → SrcState → SrcState) (tgtPlug : TgtContext → TgtState → TgtState)
    (translate : SrcState → TgtState) (translateContext : SrcContext → TgtContext)
    (hpres : BisimilarityPreserving src tgt translate)
    (hreflect : BisimilarityReflecting src tgt translate)
    (hcong : Congruence tgtPlug (Bisimilar tgt))
    (hplug : ∀ C s, translate (srcPlug C s) = tgtPlug (translateContext C) (translate s)) :
    Congruence srcPlug (Bisimilar src) := by
  intro C s t hbis
  apply hreflect
  rw [hplug C s, hplug C t]
  exact hcong (translateContext C) (hpres hbis)

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

/-- Pull a fully abstract model back along a translation that preserves and reflects bisimilarity and
    commutes with contexts. A MeTTaIL-to-rho desugaring theorem can instantiate this definition once the
    translation and context correspondence are proved. -/
def pullback {SrcState : Type u} {SrcLabel : Type v} {SrcContext : Type z}
    {TgtState : Type x} {TgtLabel : Type y} {Den : Type w} {TgtContext : Type q}
    (M : FullyAbstractModel TgtState TgtLabel Den TgtContext)
    (src : LTS SrcState SrcLabel) (translate : SrcState → TgtState)
    (srcPlug : SrcContext → SrcState → SrcState) (translateContext : SrcContext → TgtContext)
    (hpres : BisimilarityPreserving src M.lts translate)
    (hreflect : BisimilarityReflecting src M.lts translate)
    (hplug : ∀ C s, translate (srcPlug C s) = M.plug (translateContext C) (translate s)) :
    FullyAbstractModel SrcState SrcLabel Den SrcContext where
  lts := src
  denote := fun s => M.denote (translate s)
  plug := srcPlug
  full :=
    fullyAbstract_of_bisimilarity_translation src M.lts M.denote translate M.full hpres hreflect
  bisim_congruent :=
    congruence_of_bisimilarity_translation src M.lts srcPlug M.plug translate translateContext hpres
      hreflect M.bisim_congruent hplug

end FullyAbstractModel

namespace PathRSpace

/-- A rho/RSpace path key is a finite list of names. The path-subspace paper uses `Name*`. -/
abbrev Path (Name : Type u) := List Name

/-- `p` is a prefix of `q` when `q` is `p` followed by a suffix. -/
def Prefix {Name : Type u} (p q : Path Name) : Prop :=
  ∃ suffix : Path Name, q = p ++ suffix

/-- Two paths are comparable when one lies under the other in the prefix tree. -/
def Comparable {Name : Type u} (p q : Path Name) : Prop :=
  Prefix p q ∨ Prefix q p

/-- Prefix is reflexive. -/
theorem prefix_refl {Name : Type u} (p : Path Name) : Prefix p p := by
  exact ⟨[], (List.append_nil p).symm⟩

/-- Prefix is transitive. -/
theorem prefix_trans {Name : Type u} {p q r : Path Name}
    (hpq : Prefix p q) (hqr : Prefix q r) : Prefix p r := by
  rcases hpq with ⟨pq, rfl⟩
  rcases hqr with ⟨qr, rfl⟩
  exact ⟨pq ++ qr, by rw [List.append_assoc]⟩

/-- Every path is comparable with itself. -/
theorem comparable_refl {Name : Type u} (p : Path Name) : Comparable p p :=
  Or.inl (prefix_refl p)

/-- Comparability is symmetric. -/
theorem comparable_symm {Name : Type u} {p q : Path Name}
    (h : Comparable p q) : Comparable q p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

/-- The two subspace COMM branches. `outDeep` is the case where the output path is deeper than the
    input path. `inDeep` is the dual case where the input path is deeper than the output path. -/
inductive SubspaceBranch {Name : Type u} (input output : Path Name) : Type u where
  | outDeep (suffix : Path Name) (h : output = input ++ suffix)
  | inDeep (suffix : Path Name) (h : input = output ++ suffix)

namespace SubspaceBranch

/-- A selected subspace branch proves path comparability. -/
theorem comparable {Name : Type u} {input output : Path Name}
    (branch : SubspaceBranch input output) : Comparable input output := by
  cases branch with
  | outDeep suffix h => exact Or.inl ⟨suffix, h⟩
  | inDeep suffix h => exact Or.inr ⟨suffix, h⟩

end SubspaceBranch

/-- Path comparability is exactly the information needed to choose one of the two subspace COMM
    branches. The theorem records the checked part of the paper's path-key matching condition. -/
theorem comparable_iff_nonempty_subspaceBranch {Name : Type u} (input output : Path Name) :
    Comparable input output ↔ Nonempty (SubspaceBranch input output) := by
  constructor
  · intro h
    cases h with
    | inl hp =>
        rcases hp with ⟨suffix, hsuffix⟩
        exact ⟨SubspaceBranch.outDeep suffix hsuffix⟩
    | inr hp =>
        rcases hp with ⟨suffix, hsuffix⟩
        exact ⟨SubspaceBranch.inDeep suffix hsuffix⟩
  · intro h
    rcases h with ⟨branch⟩
    exact SubspaceBranch.comparable branch

/-- A cut-triggered transition system. The path-subspace paper rules out ambient store reactions: every
    reaction has to come from an explicit cut. -/
def NoImplicitInteraction {State : Type u} (hasCut : State → Prop)
    (step : State → State → Prop) : Prop :=
  ∀ {s t}, step s t → hasCut s

/-- The abstract interface for the path-key RSpace refinement. A concrete model must say which cut is
    present, which input/output paths the cut exposes, and prove that every step is both cut-triggered
    and comparable in the prefix order. -/
structure SubspaceSystem (Name : Type u) (State : Type v) where
  hasCut : State → Prop
  inputPath : State → Path Name
  outputPath : State → Path Name
  step : State → State → Prop
  no_implicit_interaction : NoImplicitInteraction hasCut step
  comparable_of_step : ∀ {s t}, step s t → Comparable (inputPath s) (outputPath s)

namespace SubspaceSystem

/-- A path-subspace step chooses one of the two COMM branches. -/
theorem branch_of_step {Name : Type u} {State : Type v} (S : SubspaceSystem Name State)
    {s t : State} (h : S.step s t) :
    Nonempty (SubspaceBranch (S.inputPath s) (S.outputPath s)) :=
  (comparable_iff_nonempty_subspaceBranch (S.inputPath s) (S.outputPath s)).1
    (S.comparable_of_step h)

end SubspaceSystem

end PathRSpace

namespace Costed

/-- A labelled transition system whose steps carry a cost. The cost-accounting papers use this kind of
    layer for phlogiston, token stacks, and other metered reductions. -/
structure CostedLTS (State : Type u) (Label : Type v) (Cost : Type w) where
  step : State → Label → Cost → State → Prop

/-- Drop the cost annotation and keep the behaviour. -/
def CostedLTS.forget {State : Type u} {Label : Type v} {Cost : Type w}
    (clts : CostedLTS State Label Cost) : LTS State Label where
  step s l t := ∃ cost, clts.step s l cost t

/-- The unlabelled one-step relation induced by an LTS. -/
def Step {State : Type u} {Label : Type v} (lts : LTS State Label) : State → State → Prop :=
  fun s t => ∃ label, lts.step s label t

/-- The unlabelled one-step relation induced by a costed LTS. -/
def CostedStep {State : Type u} {Label : Type v} {Cost : Type w}
    (clts : CostedLTS State Label Cost) : State → State → Prop :=
  fun s t => ∃ label cost, clts.step s label cost t

/-- A costed step is an ordinary step after forgetting the cost. -/
theorem costedStep_forget {State : Type u} {Label : Type v} {Cost : Type w}
    (clts : CostedLTS State Label Cost) {s t : State} :
    CostedStep clts s t ↔ Step clts.forget s t := by
  constructor
  · intro h
    rcases h with ⟨label, cost, hstep⟩
    exact ⟨label, cost, hstep⟩
  · intro h
    rcases h with ⟨label, cost, hstep⟩
    exact ⟨label, cost, hstep⟩

/-- A finite costed trace. The cost annotation is accumulated along the trace. -/
inductive Trace {State : Type u} {Label : Type v} {Cost : Type w} [Zero Cost] [Add Cost]
    (clts : CostedLTS State Label Cost) : State → Cost → State → Prop where
  | refl (s : State) : Trace clts s 0 s
  | tail {s t u : State} (label : Label) (cost total : Cost) :
      clts.step s label cost t → Trace clts t total u → Trace clts s (cost + total) u

namespace Trace

/-- A costed trace projects to an ordinary behavioural trace once costs are forgotten. -/
theorem to_reflTransGen {State : Type u} {Label : Type v} {Cost : Type w} [Zero Cost] [Add Cost]
    {clts : CostedLTS State Label Cost} {s t : State} {total : Cost}
    (h : Trace clts s total t) :
    Relation.ReflTransGen (Step clts.forget) s t := by
  induction h with
  | refl s => exact Relation.ReflTransGen.refl
  | tail label cost total hstep _ ih =>
      exact (Relation.ReflTransGen.single ⟨label, cost, hstep⟩).trans ih

end Trace

end Costed

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
