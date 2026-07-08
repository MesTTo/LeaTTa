-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Semantics.NativeTypes
Layer: Semantics
Purpose: Native OSLF types over MeTTaIL presentations.
  Native Type Theory builds type constructors from term constructors and predicate logic. OSLF reads
  those predicates over a calculus presentation. This file records the shared Lean surface for the
  runtime: a native type is a presentation sort paired with an OSLF predicate over `AST`.
Imports: MeTTaIL.Semantics.OSLF, MeTTaIL.Semantics.Sorts, MeTTaIL.Semantics.NativeGrammar
Trusted boundary: none
Main exports: OSLF.Pred.future, OSLF.Pred.pastBox, OSLF.Pred.future_box_galois,
  OSLF.Pred.dia_pastBox_galois, OSLF.NativeType, OSLF.NativeType.constructor,
  OSLF.NativeType.arrow, OSLF.forwardGaloisBridge, OSLF.possiblePastGaloisBridge
Open obligations: instantiate the constructors from generated `Presentation.terms`, connect this
  predicate layer to recursive well-sortedness, and plug it into concrete surface parsers.
-/
import MeTTaIL.Semantics.OSLF
import MeTTaIL.Semantics.Sorts
import MeTTaIL.Semantics.NativeGrammar

namespace MeTTaIL
namespace OSLF

namespace Pred

/-- Forward image of a predicate along many-step reduction. -/
def future (p : Presentation) (A : Pred) : Pred :=
  fun t => ∃ s, RewStepMany p s t ∧ A s

/-- Past necessity: every predecessor of the current term satisfies `A`. -/
def pastBox (p : Presentation) (A : Pred) : Pred :=
  fun t => ∀ s, RewStepMany p s t → A s

/-- Forward image is left adjoint to the existing future-safety box. -/
theorem future_box_galois (p : Presentation) :
    GaloisConnection (future p) (box p) := by
  intro A B
  constructor
  · intro h t ht t' hstep
    exact h t' ⟨t, hstep, ht⟩
  · intro h t ht
    rcases ht with ⟨s, hstep, hs⟩
    exact h s hs t hstep

/-- The existing possible-future diamond is left adjoint to past necessity. -/
theorem dia_pastBox_galois (p : Presentation) :
    GaloisConnection (dia p) (pastBox p) := by
  intro A B
  constructor
  · intro h t ht s hstep
    exact h s ⟨t, hstep, ht⟩
  · intro h t ht
    rcases ht with ⟨s, hstep, hs⟩
    exact h s hs t hstep

/-- The unit for `future ⊣ box`: a predicate implies `box (future A)`. -/
theorem le_box_future (p : Presentation) (A : Pred) :
    A ≤ box p (future p A) :=
  (future_box_galois p).le_u_l A

/-- The counit for `future ⊣ box`: `future (box A)` implies `A`. -/
theorem future_box_le (p : Presentation) (A : Pred) :
    future p (box p A) ≤ A :=
  (future_box_galois p).l_u_le A

/-- The unit for `dia ⊣ pastBox`: a predicate implies `pastBox (dia A)`. -/
theorem le_pastBox_dia (p : Presentation) (A : Pred) :
    A ≤ pastBox p (dia p A) :=
  (dia_pastBox_galois p).le_u_l A

/-- The counit for `dia ⊣ pastBox`: `dia (pastBox A)` implies `A`. -/
theorem dia_pastBox_le (p : Presentation) (A : Pred) :
    dia p (pastBox p A) ≤ A :=
  (dia_pastBox_galois p).l_u_le A

end Pred

/-- The outer constructor label of a term, when it has one. -/
def headLabel? : AST → Option Label
  | .sexp label _ => some label
  | _ => none

/-- A native OSLF type is a sort plus a predicate over MeTTaIL terms. -/
structure NativeType where
  sort : Cat
  pred : Pred

namespace NativeType

/-- A term satisfies a native type when it satisfies the predicate component. -/
def satisfies (A : NativeType) (t : AST) : Prop :=
  A.pred t

/-- A term satisfies a native type at the presentation level when its head sort also matches. -/
def sortedSatisfies (p : Presentation) (A : NativeType) (t : AST) : Prop :=
  AST.headCat p.terms t = some A.sort ∧ A.satisfies t

/-- Build a native type from a sort and a predicate. -/
def ofPred (sort : Cat) (pred : Pred) : NativeType where
  sort := sort
  pred := pred

/-- The full native type over a sort. -/
def top (sort : Cat) : NativeType :=
  ofPred sort Pred.top

/-- The empty native type over a sort. -/
def bot (sort : Cat) : NativeType :=
  ofPred sort Pred.bot

/-- Native conjunction keeps the left sort and intersects predicates. -/
def conj (A B : NativeType) : NativeType :=
  ofPred A.sort (Pred.conj A.pred B.pred)

/-- Native disjunction keeps the left sort and unions predicates. -/
def disj (A B : NativeType) : NativeType :=
  ofPred A.sort (Pred.disj A.pred B.pred)

/-- Native negation keeps the same sort and complements the predicate. -/
def neg (A : NativeType) : NativeType :=
  ofPred A.sort (Pred.neg A.pred)

/-- A constructor-derived native type. -/
def constructor (sort : Cat) (label : Label) : NativeType :=
  ofPred sort (fun t => headLabel? t = some label)

/-- Spatial composition under a binary constructor. -/
def spatial (sort : Cat) (label : Label) (A B : NativeType) : NativeType :=
  ofPred sort (Pred.spatial label A.pred B.pred)

/-- OSLF possible-future modality lifted to native types. -/
def dia (p : Presentation) (A : NativeType) : NativeType :=
  ofPred A.sort (Pred.dia p A.pred)

/-- OSLF future-safety modality lifted to native types. -/
def box (p : Presentation) (A : NativeType) : NativeType :=
  ofPred A.sort (Pred.box p A.pred)

/-- Forward image along reduction, paired with `box` by `future_box_galois`. -/
def future (p : Presentation) (A : NativeType) : NativeType :=
  ofPred A.sort (Pred.future p A.pred)

/-- Past necessity, paired with `dia` by `dia_pastBox_galois`. -/
def pastBox (p : Presentation) (A : NativeType) : NativeType :=
  ofPred A.sort (Pred.pastBox p A.pred)

/-- The OSLF behavioral arrow as a native type. -/
def arrow (p : Presentation) (app : Label) (A B : NativeType) : NativeType :=
  ofPred (.arrow A.sort B.sort) (Pred.arrow p app A.pred B.pred)

/-- Satisfaction unfolds to the predicate component. -/
theorem satisfies_iff (A : NativeType) (t : AST) :
    A.satisfies t ↔ A.pred t :=
  Iff.rfl

/-- Sorted satisfaction is head-sort matching plus predicate satisfaction. -/
theorem sortedSatisfies_iff (p : Presentation) (A : NativeType) (t : AST) :
    A.sortedSatisfies p t ↔ AST.headCat p.terms t = some A.sort ∧ A.satisfies t :=
  Iff.rfl

/-- Constructor type satisfaction is exactly head-label equality. -/
theorem constructor_satisfies_iff (sort : Cat) (label : Label) (t : AST) :
    (constructor sort label).satisfies t ↔ headLabel? t = some label :=
  Iff.rfl

/-- A constructor application satisfies its own constructor type. -/
theorem constructor_satisfies_self (sort : Cat) (label : Label) (args : List AST) :
    (constructor sort label).satisfies (.sexp label args) := by
  rfl

/-- Spatial type satisfaction is the OSLF spatial predicate. -/
theorem spatial_satisfies_iff
    (sort : Cat) (label : Label) (A B : NativeType) (t : AST) :
    (spatial sort label A B).satisfies t ↔ Pred.spatial label A.pred B.pred t :=
  Iff.rfl

/-- A binary constructor satisfies the spatial native type iff its children satisfy the inputs. -/
theorem spatial_satisfies_sexp_iff
    (sort : Cat) (label : Label) (A B : NativeType) (a b : AST) :
    (spatial sort label A B).satisfies (.sexp label [a, b]) ↔ A.satisfies a ∧ B.satisfies b := by
  change Pred.spatial label A.pred B.pred (.sexp label [a, b]) ↔ A.pred a ∧ B.pred b
  exact sat_spatial label A.pred B.pred a b

/-- Native arrow satisfaction is the OSLF behavioral arrow. -/
theorem arrow_satisfies_iff
    (p : Presentation) (app : Label) (A B : NativeType) (t : AST) :
    (arrow p app A B).satisfies t ↔ Pred.arrow p app A.pred B.pred t :=
  Iff.rfl

/-- Native diamond satisfaction is OSLF diamond satisfaction. -/
theorem dia_satisfies_iff (p : Presentation) (A : NativeType) (t : AST) :
    (dia p A).satisfies t ↔ Pred.dia p A.pred t :=
  Iff.rfl

/-- Native box satisfaction is OSLF box satisfaction. -/
theorem box_satisfies_iff (p : Presentation) (A : NativeType) (t : AST) :
    (box p A).satisfies t ↔ Pred.box p A.pred t :=
  Iff.rfl

/-- Native forward-image satisfaction is OSLF forward-image satisfaction. -/
theorem future_satisfies_iff (p : Presentation) (A : NativeType) (t : AST) :
    (future p A).satisfies t ↔ Pred.future p A.pred t :=
  Iff.rfl

/-- Native past-box satisfaction is OSLF past-box satisfaction. -/
theorem pastBox_satisfies_iff (p : Presentation) (A : NativeType) (t : AST) :
    (pastBox p A).satisfies t ↔ Pred.pastBox p A.pred t :=
  Iff.rfl

/-- The runtime preserves sorted satisfaction for a boxed native type. -/
theorem sortedBox_preserved (p : Presentation) (A : NativeType)
    (hSort : SortPreserving p) {t t' : AST} (hstep : RewStepMany p t t') :
    (box p A).sortedSatisfies p t → (box p A).sortedSatisfies p t' := by
  intro h
  exact ⟨(rewStepMany_preserves_headCat hSort hstep).symm.trans h.1,
    box_preserved p A.pred hstep h.2⟩

end NativeType

/-- The forward-image and future-safety modalities as a packaged native Galois bridge. -/
def forwardGaloisBridge (p : Presentation) :
    Denotational.NativeGaloisBridge Pred Pred where
  diamond := Pred.future p
  box := Pred.box p
  adjunction := Pred.future_box_galois p

/-- The possible-future and past-necessity modalities as a packaged native Galois bridge. -/
def possiblePastGaloisBridge (p : Presentation) :
    Denotational.NativeGaloisBridge Pred Pred where
  diamond := Pred.dia p
  box := Pred.pastBox p
  adjunction := Pred.dia_pastBox_galois p

end OSLF
end MeTTaIL
