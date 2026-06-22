/-
Module: MeTTaIL.Semantics.KnottedUniverse
Layer: Semantics
Purpose: Checked red/black and final-coalgebra interfaces for the knotted-universe route.
  The source papers use four sorts: red sets, red atoms, black sets, and black atoms. Red
  atoms are black sets seen opaquely, and black atoms are red sets seen opaquely. The rho
  denotation then targets a final behaviour coalgebra. This file records those interfaces and
  the round-trip laws they force. It also gives coalgebras their standard morphisms and
  category instance, so `FinalCoalgebra` can be read as a terminal object there. It does not
  construct the knotted topos.
Imports: MeTTaIL.Semantics.Denotational, Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
  Mathlib.Logic.Equiv.Basic
Trusted boundary: none
Main exports: Colour, Colour.swap, Colour.swap_swap, ReflectiveUniverse,
  ReflectiveUniverse.dropRed_quoteRed, ReflectiveUniverse.quoteRed_dropRed,
  ReflectiveUniverse.dropBlack_quoteBlack, ReflectiveUniverse.quoteBlack_dropBlack,
  ReflectiveUniverseHom, ReflectiveUniverse.category,
  TypeEndofunctor, Coalgebra, CoalgebraHom, Coalgebra.category, FinalCoalgebra,
  FinalCoalgebra.finalHom, FinalCoalgebra.finalHom_unique, FinalCoalgebra.isTerminal,
  FinalBehaviourModel, FinalBehaviourModel.fullyAbstractFor,
  FinalBehaviourModel.fullyAbstractForObservations
Open obligations: instantiate ReflectiveUniverse with the knotted topos, prove that the behaviour
  functor has the intended final coalgebra there, and connect the resulting denotation to the
  MeTTaIL-to-rho operational correspondence.
-/
import MeTTaIL.Semantics.Denotational
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Logic.Equiv.Basic

namespace MeTTaIL
namespace KnottedUniverse

universe u v w z r

/-- The two colours used by the red/black reflective universe papers. -/
inductive Colour where
  | red
  | black
  deriving DecidableEq, Repr

namespace Colour

/-- Swap to the opposite colour. -/
def swap : Colour → Colour
  | red => black
  | black => red

/-- Colour swap is an involution. -/
theorem swap_swap (c : Colour) : swap (swap c) = c := by
  cases c <;> rfl

end Colour

/-- The four visible sorts of the knotted-universe surface. -/
structure ReflectiveUniverse where
  RedSet : Type u
  RedAtom : Type u
  BlackSet : Type u
  BlackAtom : Type u
  redAtomsAsBlackSets : RedAtom ≃ BlackSet
  blackAtomsAsRedSets : BlackAtom ≃ RedSet
  redBlackSetSwap : RedSet ≃ BlackSet
  redBlackAtomSwap : RedAtom ≃ BlackAtom

namespace ReflectiveUniverse

/-- A colour-indexed view of the set sorts. -/
def Set (U : ReflectiveUniverse.{u}) : Colour → Type u
  | Colour.red => U.RedSet
  | Colour.black => U.BlackSet

/-- A colour-indexed view of the atom sorts. -/
def Atom (U : ReflectiveUniverse.{u}) : Colour → Type u
  | Colour.red => U.RedAtom
  | Colour.black => U.BlackAtom

/-- Seal a black set as an opaque red atom. -/
def quoteRed (U : ReflectiveUniverse.{u}) : U.BlackSet → U.RedAtom :=
  U.redAtomsAsBlackSets.symm

/-- Open an opaque red atom as the black set it names. -/
def dropRed (U : ReflectiveUniverse.{u}) : U.RedAtom → U.BlackSet :=
  U.redAtomsAsBlackSets

/-- Seal a red set as an opaque black atom. -/
def quoteBlack (U : ReflectiveUniverse.{u}) : U.RedSet → U.BlackAtom :=
  U.blackAtomsAsRedSets.symm

/-- Open an opaque black atom as the red set it names. -/
def dropBlack (U : ReflectiveUniverse.{u}) : U.BlackAtom → U.RedSet :=
  U.blackAtomsAsRedSets

/-- Dropping a quoted black set returns that black set. -/
theorem dropRed_quoteRed (U : ReflectiveUniverse.{u}) (x : U.BlackSet) :
    U.dropRed (U.quoteRed x) = x :=
  U.redAtomsAsBlackSets.right_inv x

/-- Quoting a dropped red atom returns that red atom. -/
theorem quoteRed_dropRed (U : ReflectiveUniverse.{u}) (a : U.RedAtom) :
    U.quoteRed (U.dropRed a) = a :=
  U.redAtomsAsBlackSets.left_inv a

/-- Dropping a quoted red set returns that red set. -/
theorem dropBlack_quoteBlack (U : ReflectiveUniverse.{u}) (x : U.RedSet) :
    U.dropBlack (U.quoteBlack x) = x :=
  U.blackAtomsAsRedSets.right_inv x

/-- Quoting a dropped black atom returns that black atom. -/
theorem quoteBlack_dropBlack (U : ReflectiveUniverse.{u}) (a : U.BlackAtom) :
    U.quoteBlack (U.dropBlack a) = a :=
  U.blackAtomsAsRedSets.left_inv a

/-- The one-sort model shows the interface is consistent, but it is not the knotted topos. -/
def constant (A : Type u) : ReflectiveUniverse.{u} where
  RedSet := A
  RedAtom := A
  BlackSet := A
  BlackAtom := A
  redAtomsAsBlackSets := Equiv.refl A
  blackAtomsAsRedSets := Equiv.refl A
  redBlackSetSwap := Equiv.refl A
  redBlackAtomSwap := Equiv.refl A

end ReflectiveUniverse

/-- A structure-preserving map between red/black reflective universes. -/
structure ReflectiveUniverseHom (U V : ReflectiveUniverse.{u}) where
  redSet : U.RedSet → V.RedSet
  redAtom : U.RedAtom → V.RedAtom
  blackSet : U.BlackSet → V.BlackSet
  blackAtom : U.BlackAtom → V.BlackAtom
  quoteRed_comm : ∀ x, redAtom (U.quoteRed x) = V.quoteRed (blackSet x)
  dropRed_comm : ∀ a, blackSet (U.dropRed a) = V.dropRed (redAtom a)
  quoteBlack_comm : ∀ x, blackAtom (U.quoteBlack x) = V.quoteBlack (redSet x)
  dropBlack_comm : ∀ a, redSet (U.dropBlack a) = V.dropBlack (blackAtom a)
  redBlackSetSwap_comm : ∀ x, blackSet (U.redBlackSetSwap x) = V.redBlackSetSwap (redSet x)
  blackRedSetSwap_comm : ∀ x, redSet (U.redBlackSetSwap.symm x) =
    V.redBlackSetSwap.symm (blackSet x)
  redBlackAtomSwap_comm : ∀ a, blackAtom (U.redBlackAtomSwap a) =
    V.redBlackAtomSwap (redAtom a)
  blackRedAtomSwap_comm : ∀ a, redAtom (U.redBlackAtomSwap.symm a) =
    V.redBlackAtomSwap.symm (blackAtom a)

namespace ReflectiveUniverseHom

/-- The identity reflective-universe morphism. -/
def id (U : ReflectiveUniverse.{u}) : ReflectiveUniverseHom U U where
  redSet := fun x => x
  redAtom := fun x => x
  blackSet := fun x => x
  blackAtom := fun x => x
  quoteRed_comm _ := rfl
  dropRed_comm _ := rfl
  quoteBlack_comm _ := rfl
  dropBlack_comm _ := rfl
  redBlackSetSwap_comm _ := rfl
  blackRedSetSwap_comm _ := rfl
  redBlackAtomSwap_comm _ := rfl
  blackRedAtomSwap_comm _ := rfl

/-- Compose reflective-universe morphisms in diagram order. -/
def comp {U V W : ReflectiveUniverse.{u}}
    (g : ReflectiveUniverseHom V W) (f : ReflectiveUniverseHom U V) :
    ReflectiveUniverseHom U W where
  redSet := g.redSet ∘ f.redSet
  redAtom := g.redAtom ∘ f.redAtom
  blackSet := g.blackSet ∘ f.blackSet
  blackAtom := g.blackAtom ∘ f.blackAtom
  quoteRed_comm := by
    intro x
    calc
      g.redAtom (f.redAtom (U.quoteRed x)) = g.redAtom (V.quoteRed (f.blackSet x)) := by
        rw [f.quoteRed_comm x]
      _ = W.quoteRed (g.blackSet (f.blackSet x)) := by
        rw [g.quoteRed_comm (f.blackSet x)]
  dropRed_comm := by
    intro a
    calc
      g.blackSet (f.blackSet (U.dropRed a)) = g.blackSet (V.dropRed (f.redAtom a)) := by
        rw [f.dropRed_comm a]
      _ = W.dropRed (g.redAtom (f.redAtom a)) := by
        rw [g.dropRed_comm (f.redAtom a)]
  quoteBlack_comm := by
    intro x
    calc
      g.blackAtom (f.blackAtom (U.quoteBlack x)) = g.blackAtom (V.quoteBlack (f.redSet x)) := by
        rw [f.quoteBlack_comm x]
      _ = W.quoteBlack (g.redSet (f.redSet x)) := by
        rw [g.quoteBlack_comm (f.redSet x)]
  dropBlack_comm := by
    intro a
    calc
      g.redSet (f.redSet (U.dropBlack a)) = g.redSet (V.dropBlack (f.blackAtom a)) := by
        rw [f.dropBlack_comm a]
      _ = W.dropBlack (g.blackAtom (f.blackAtom a)) := by
        rw [g.dropBlack_comm (f.blackAtom a)]
  redBlackSetSwap_comm := by
    intro x
    calc
      g.blackSet (f.blackSet (U.redBlackSetSwap x)) =
          g.blackSet (V.redBlackSetSwap (f.redSet x)) := by
        rw [f.redBlackSetSwap_comm x]
      _ = W.redBlackSetSwap (g.redSet (f.redSet x)) := by
        rw [g.redBlackSetSwap_comm (f.redSet x)]
  blackRedSetSwap_comm := by
    intro x
    calc
      g.redSet (f.redSet (U.redBlackSetSwap.symm x)) =
          g.redSet (V.redBlackSetSwap.symm (f.blackSet x)) := by
        rw [f.blackRedSetSwap_comm x]
      _ = W.redBlackSetSwap.symm (g.blackSet (f.blackSet x)) := by
        rw [g.blackRedSetSwap_comm (f.blackSet x)]
  redBlackAtomSwap_comm := by
    intro a
    calc
      g.blackAtom (f.blackAtom (U.redBlackAtomSwap a)) =
          g.blackAtom (V.redBlackAtomSwap (f.redAtom a)) := by
        rw [f.redBlackAtomSwap_comm a]
      _ = W.redBlackAtomSwap (g.redAtom (f.redAtom a)) := by
        rw [g.redBlackAtomSwap_comm (f.redAtom a)]
  blackRedAtomSwap_comm := by
    intro a
    calc
      g.redAtom (f.redAtom (U.redBlackAtomSwap.symm a)) =
          g.redAtom (V.redBlackAtomSwap.symm (f.blackAtom a)) := by
        rw [f.blackRedAtomSwap_comm a]
      _ = W.redBlackAtomSwap.symm (g.blackAtom (f.blackAtom a)) := by
        rw [g.blackRedAtomSwap_comm (f.blackAtom a)]

/-- Reflective-universe morphisms are equal when their four component maps are pointwise equal. -/
@[ext]
theorem ext {U V : ReflectiveUniverse.{u}} {f g : ReflectiveUniverseHom U V}
    (hRedSet : ∀ x, f.redSet x = g.redSet x)
    (hRedAtom : ∀ x, f.redAtom x = g.redAtom x)
    (hBlackSet : ∀ x, f.blackSet x = g.blackSet x)
    (hBlackAtom : ∀ x, f.blackAtom x = g.blackAtom x) : f = g := by
  cases f with
  | mk frs fra fbs fba =>
    cases g with
    | mk grs gra gbs gba =>
      dsimp at hRedSet hRedAtom hBlackSet hBlackAtom
      have hrs : frs = grs := funext hRedSet
      have hra : fra = gra := funext hRedAtom
      have hbs : fbs = gbs := funext hBlackSet
      have hba : fba = gba := funext hBlackAtom
      cases hrs
      cases hra
      cases hbs
      cases hba
      rfl

end ReflectiveUniverseHom

namespace ReflectiveUniverse

/-- Reflective universes and structure-preserving maps form a category. -/
instance category : CategoryTheory.Category.{u} ReflectiveUniverse.{u} where
  Hom U V := ReflectiveUniverseHom U V
  id U := ReflectiveUniverseHom.id U
  comp f g := ReflectiveUniverseHom.comp g f
  id_comp := by
    intro U V f
    ext x <;> rfl
  comp_id := by
    intro U V f
    ext x <;> rfl
  assoc := by
    intro U V W X f g h
    ext x <;> rfl

end ReflectiveUniverse

/-- An endofunctor on `Type`. The final-behaviour object is final for such a functor. -/
structure TypeEndofunctor where
  obj : Type u → Type u
  map : {α β : Type u} → (α → β) → obj α → obj β
  map_id : ∀ {α : Type u} (x : obj α), map id x = x
  map_comp : ∀ {α β γ : Type u} (f : α → β) (g : β → γ) (x : obj α),
    map (g ∘ f) x = map g (map f x)

namespace TypeEndofunctor

/-- The identity endofunctor on `Type`. -/
def identity : TypeEndofunctor.{u} where
  obj α := α
  map f x := f x
  map_id _ := rfl
  map_comp _ _ _ := rfl

end TypeEndofunctor

/-- A coalgebra for an endofunctor. -/
structure Coalgebra (F : TypeEndofunctor.{u}) where
  carrier : Type u
  out : carrier → F.obj carrier

/-- A morphism of coalgebras. -/
structure CoalgebraHom {F : TypeEndofunctor.{u}} (C D : Coalgebra F) where
  map : C.carrier → D.carrier
  comm : ∀ x, D.out (map x) = F.map map (C.out x)

namespace CoalgebraHom

/-- The identity coalgebra morphism. -/
def id {F : TypeEndofunctor.{u}} (C : Coalgebra F) : CoalgebraHom C C where
  map := fun x => x
  comm := by
    intro x
    exact (F.map_id (C.out x)).symm

/-- Compose coalgebra morphisms in diagram order. -/
def comp {F : TypeEndofunctor.{u}} {A B C : Coalgebra F}
    (g : CoalgebraHom B C) (f : CoalgebraHom A B) : CoalgebraHom A C where
  map := g.map ∘ f.map
  comm := by
    intro x
    calc
      C.out (g.map (f.map x)) = F.map g.map (B.out (f.map x)) := g.comm (f.map x)
      _ = F.map g.map (F.map f.map (A.out x)) := by rw [f.comm x]
      _ = F.map (g.map ∘ f.map) (A.out x) := by
        exact (F.map_comp f.map g.map (A.out x)).symm

/-- Coalgebra morphisms are equal when their maps are pointwise equal. -/
@[ext]
theorem ext {F : TypeEndofunctor.{u}} {C D : Coalgebra F} {f g : CoalgebraHom C D}
    (h : ∀ x, f.map x = g.map x) : f = g := by
  cases f with
  | mk fmap fcomm =>
    cases g with
    | mk gmap gcomm =>
      dsimp at h
      have hmap : fmap = gmap := funext h
      cases hmap
      rfl

end CoalgebraHom

namespace Coalgebra

/-- Coalgebras and coalgebra morphisms form a category. -/
instance category (F : TypeEndofunctor.{u}) : CategoryTheory.Category.{u} (Coalgebra F) where
  Hom C D := CoalgebraHom C D
  id C := CoalgebraHom.id C
  comp f g := CoalgebraHom.comp g f
  id_comp := by
    intro X Y f
    ext x
    rfl
  comp_id := by
    intro X Y f
    ext x
    rfl
  assoc := by
    intro W X Y Z f g h
    ext x
    rfl

end Coalgebra

/-- A final coalgebra, stated by its universal map from every coalgebra. -/
structure FinalCoalgebra (F : TypeEndofunctor.{u}) where
  terminal : Coalgebra F
  lift : (C : Coalgebra F) → C.carrier → terminal.carrier
  lift_comm : ∀ (C : Coalgebra F) (x : C.carrier),
    terminal.out (lift C x) = F.map (lift C) (C.out x)
  lift_unique : ∀ (C : Coalgebra F) (f : C.carrier → terminal.carrier),
    (∀ x, terminal.out (f x) = F.map f (C.out x)) → f = lift C

namespace FinalCoalgebra

/-- The final map is a coalgebra morphism. -/
theorem lift_commutes {F : TypeEndofunctor.{u}} (νF : FinalCoalgebra F)
    (C : Coalgebra F) (x : C.carrier) :
    νF.terminal.out (νF.lift C x) = F.map (νF.lift C) (C.out x) :=
  νF.lift_comm C x

/-- The final map, packaged as a coalgebra morphism. -/
def finalHom {F : TypeEndofunctor.{u}} (final : FinalCoalgebra F)
    (C : Coalgebra F) : CoalgebraHom C final.terminal where
  map := final.lift C
  comm := final.lift_comm C

/-- Every coalgebra morphism into the final coalgebra is the final map. -/
theorem finalHom_unique {F : TypeEndofunctor.{u}} (final : FinalCoalgebra F)
    (C : Coalgebra F) (h : CoalgebraHom C final.terminal) :
    h = final.finalHom C := by
  apply CoalgebraHom.ext
  intro x
  exact congrFun (final.lift_unique C h.map h.comm) x

/-- The final coalgebra is terminal in the category of coalgebras. -/
def isTerminal {F : TypeEndofunctor.{u}} (final : FinalCoalgebra F) :
    CategoryTheory.Limits.IsTerminal final.terminal :=
  CategoryTheory.Limits.IsTerminal.ofUniqueHom
    (fun C => final.finalHom C)
    (fun C h => final.finalHom_unique C h)

/-- `PUnit` is the final coalgebra for the identity functor. This checks the universal-property shape. -/
def identity : FinalCoalgebra TypeEndofunctor.identity where
  terminal :=
    { carrier := PUnit
      out := id }
  lift _ _ := PUnit.unit
  lift_comm _ _ := rfl
  lift_unique C f _ := by
    funext x
    cases f x
    rfl

end FinalCoalgebra

/-- A behaviour model whose denotation is the unique map into a final coalgebra. -/
structure FinalBehaviourModel (State : Type u) (Label : Type v) (Context : Type z) where
  F : TypeEndofunctor.{w}
  system : Coalgebra F
  final : FinalCoalgebra F
  lts : Denotational.LTS State Label
  encode : State → system.carrier
  plug : Context → State → State
  full : Denotational.FullyAbstract lts (fun s => final.lift system (encode s))
  bisim_congruent : Denotational.Congruence plug (Denotational.Bisimilar lts)

namespace FinalBehaviourModel

/-- The denotation induced by finality. -/
def denote {State : Type u} {Label : Type v} {Context : Type z}
    (M : FinalBehaviourModel.{u, v, w, z} State Label Context) :
    State → M.final.terminal.carrier :=
  fun s => M.final.lift M.system (M.encode s)

/-- A final-behaviour model is a fully abstract denotational model. -/
def toFullyAbstractModel {State : Type u} {Label : Type v} {Context : Type z}
    (M : FinalBehaviourModel.{u, v, w, z} State Label Context) :
    Denotational.FullyAbstractModel State Label M.final.terminal.carrier Context where
  lts := M.lts
  denote := M.denote
  plug := M.plug
  full := M.full
  bisim_congruent := M.bisim_congruent

/-- The packaged model exposes the same full-abstraction equation. -/
theorem eq_iff_bisimilar {State : Type u} {Label : Type v} {Context : Type z}
    (M : FinalBehaviourModel.{u, v, w, z} State Label Context) (s t : State) :
    M.denote s = M.denote t ↔ Denotational.Bisimilar M.lts s t :=
  M.full s t

/-- Calibrate the final-behaviour denotation against a chosen object-language equivalence. -/
theorem fullyAbstractFor {State : Type u} {Label : Type v} {Context : Type z}
    {obsEq : State → State → Prop}
    (M : FinalBehaviourModel.{u, v, w, z} State Label Context)
    (cal : Denotational.BisimilarityCalibration M.lts obsEq) :
    Denotational.FullyAbstractFor M.denote obsEq :=
  Denotational.fullyAbstract_of_calibration M.full cal

/-- Calibrate the final-behaviour denotation against an observation family. -/
theorem fullyAbstractForObservations {State : Type u} {Label : Type v} {Context : Type z}
    {Observation : Type r} {observes : Observation → State → Prop}
    (M : FinalBehaviourModel.{u, v, w, z} State Label Context)
    (cal : Denotational.ObservationCalibration M.lts observes) :
    Denotational.FullyAbstractFor M.denote (Denotational.ObservationalEquivalence observes) :=
  Denotational.fullyAbstract_of_observation_calibration M.full cal

end FinalBehaviourModel

end KnottedUniverse
end MeTTaIL
