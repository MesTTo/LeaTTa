/-
Module: MeTTaIL.Semantics.Native
Layer: Semantics
Purpose: The semantic boundary for native carriers inside a MeTTaIL presentation.
  A native carrier is not accepted as a host-language shortcut. It has to embed into the source
  transition system, match source steps in both directions on embedded states, preserve its native
  type assignment, and commute with the source context operation. Those are the obligations needed
  before the existing full-abstraction package can be pulled back to the native surface.
Imports: MeTTaIL.Semantics.Denotational
Trusted boundary: none
Main exports: Denotational.StepTranslation, Denotational.StepTranslation.bisimilarityPreserving,
  Denotational.StepTranslation.bisimilarityReflecting, Denotational.NativeCarrier,
  Denotational.NativeCarrier.toFullyAbstractModel, Denotational.NativeCarrier.eq_iff_bisimilar
Open obligations: instantiate this boundary for concrete native MeTTaIL carriers, then connect those
  instances to the rho/RSpace desugaring and the knotted-topos behaviour object.
-/
import MeTTaIL.Semantics.Denotational

namespace MeTTaIL
namespace Denotational

universe u v w x y z q

/-- A translated transition system matches target steps exactly on translated states. -/
structure StepTranslation {SrcState : Type u} {TgtState : Type x} {Label : Type v}
    (src : LTS SrcState Label) (tgt : LTS TgtState Label)
    (translate : SrcState → TgtState) where
  to_target : ∀ {s l s'}, src.step s l s' → tgt.step (translate s) l (translate s')
  from_target : ∀ {s l t'}, tgt.step (translate s) l t' →
    ∃ s', src.step s l s' ∧ t' = translate s'

namespace StepTranslation

/-- Exact step translation preserves bisimilarity. -/
theorem bisimilarityPreserving {SrcState : Type u} {TgtState : Type x} {Label : Type v}
    {src : LTS SrcState Label} {tgt : LTS TgtState Label} {translate : SrcState → TgtState}
    (T : StepTranslation src tgt translate) :
    BisimilarityPreserving src tgt translate := by
  intro s t hbis
  rcases hbis with ⟨R, hR, hst⟩
  refine ⟨fun x y => ∃ a b, x = translate a ∧ y = translate b ∧ R a b, ?_, ?_⟩
  · constructor
    · intro x y hxy
      rcases hxy with ⟨a, b, rfl, rfl, hab⟩
      exact ⟨b, a, rfl, rfl, hR.1 hab⟩
    · intro x y l x' hxy hstep
      rcases hxy with ⟨a, b, rfl, rfl, hab⟩
      rcases T.from_target hstep with ⟨a', ha', htarget⟩
      subst htarget
      rcases hR.2 hab ha' with ⟨b', hb', hab'⟩
      exact ⟨translate b', T.to_target hb', ⟨a', b', rfl, rfl, hab'⟩⟩
  · exact ⟨s, t, rfl, rfl, hst⟩

/-- Exact step translation reflects bisimilarity. -/
theorem bisimilarityReflecting {SrcState : Type u} {TgtState : Type x} {Label : Type v}
    {src : LTS SrcState Label} {tgt : LTS TgtState Label} {translate : SrcState → TgtState}
    (T : StepTranslation src tgt translate) :
    BisimilarityReflecting src tgt translate := by
  intro s t hbis
  refine ⟨fun a b => Bisimilar tgt (translate a) (translate b), ?_, hbis⟩
  constructor
  · intro a b hab
    exact Bisimilar.symm hab
  · intro a b l a' hab hstep
    rcases hab with ⟨R, hR, habR⟩
    rcases hR.2 habR (T.to_target hstep) with ⟨tb', htb', ha'tb'⟩
    rcases T.from_target htb' with ⟨b', hb', htb'eq⟩
    exact ⟨b', hb', ⟨R, hR, by simpa [htb'eq] using ha'tb'⟩⟩

end StepTranslation

/-- A type assignment is preserved by labelled steps. -/
def TypePreserving {State : Type u} {Label : Type v} {Ty : Type y}
    (lts : LTS State Label) (typeOf : State → Ty) : Prop :=
  ∀ {s l t}, lts.step s l t → typeOf t = typeOf s

/-- The obligations a native carrier must provide to inherit a source denotational model. -/
structure NativeCarrier (Source : Type u) (Label : Type v) (Den : Type w)
    (SourceContext : Type z) (Native : Type x) (NativeTy : Type y)
    (NativeContext : Type q) where
  source : FullyAbstractModel Source Label Den SourceContext
  nativeLTS : LTS Native Label
  embed : Native → Source
  typeOf : Native → NativeTy
  plug : NativeContext → Native → Native
  translateContext : NativeContext → SourceContext
  stepTranslation : StepTranslation nativeLTS source.lts embed
  type_preserving : TypePreserving nativeLTS typeOf
  plug_comm : ∀ C n, embed (plug C n) = source.plug (translateContext C) (embed n)

namespace NativeCarrier

/-- The native denotation is the source denotation after embedding. -/
def denote {Source : Type u} {Label : Type v} {Den : Type w} {SourceContext : Type z}
    {Native : Type x} {NativeTy : Type y} {NativeContext : Type q}
    (N : NativeCarrier Source Label Den SourceContext Native NativeTy NativeContext) :
    Native → Den :=
  fun n => N.source.denote (N.embed n)

/-- Native bisimilarity maps to source bisimilarity. -/
theorem source_bisimilar_of_native {Source : Type u} {Label : Type v} {Den : Type w}
    {SourceContext : Type z} {Native : Type x} {NativeTy : Type y} {NativeContext : Type q}
    (N : NativeCarrier Source Label Den SourceContext Native NativeTy NativeContext)
    {a b : Native} (h : Bisimilar N.nativeLTS a b) :
    Bisimilar N.source.lts (N.embed a) (N.embed b) :=
  StepTranslation.bisimilarityPreserving N.stepTranslation h

/-- Source bisimilarity on embedded native values maps back to native bisimilarity. -/
theorem native_bisimilar_of_source {Source : Type u} {Label : Type v} {Den : Type w}
    {SourceContext : Type z} {Native : Type x} {NativeTy : Type y} {NativeContext : Type q}
    (N : NativeCarrier Source Label Den SourceContext Native NativeTy NativeContext)
    {a b : Native} (h : Bisimilar N.source.lts (N.embed a) (N.embed b)) :
    Bisimilar N.nativeLTS a b :=
  StepTranslation.bisimilarityReflecting N.stepTranslation h

/-- A native carrier inherits the fully abstract source model. -/
def toFullyAbstractModel {Source : Type u} {Label : Type v} {Den : Type w}
    {SourceContext : Type z} {Native : Type x} {NativeTy : Type y} {NativeContext : Type q}
    (N : NativeCarrier Source Label Den SourceContext Native NativeTy NativeContext) :
    FullyAbstractModel Native Label Den NativeContext :=
  FullyAbstractModel.pullback N.source N.nativeLTS N.embed N.plug N.translateContext
    (StepTranslation.bisimilarityPreserving N.stepTranslation)
    (StepTranslation.bisimilarityReflecting N.stepTranslation)
    N.plug_comm

/-- The inherited model exposes denotational equality exactly as native bisimilarity. -/
theorem eq_iff_bisimilar {Source : Type u} {Label : Type v} {Den : Type w}
    {SourceContext : Type z} {Native : Type x} {NativeTy : Type y} {NativeContext : Type q}
    (N : NativeCarrier Source Label Den SourceContext Native NativeTy NativeContext)
    (a b : Native) : N.denote a = N.denote b ↔ Bisimilar N.nativeLTS a b :=
  (N.toFullyAbstractModel.full a b)

/-- Native steps preserve the carrier's native type assignment. -/
theorem typeOf_eq_of_step {Source : Type u} {Label : Type v} {Den : Type w}
    {SourceContext : Type z} {Native : Type x} {NativeTy : Type y} {NativeContext : Type q}
    (N : NativeCarrier Source Label Den SourceContext Native NativeTy NativeContext)
    {a b : Native} {l : Label} (h : N.nativeLTS.step a l b) :
    N.typeOf b = N.typeOf a :=
  N.type_preserving h

end NativeCarrier

end Denotational
end MeTTaIL
