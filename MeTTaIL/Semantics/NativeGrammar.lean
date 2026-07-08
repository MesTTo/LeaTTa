-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Semantics.NativeGrammar
Layer: Semantics
Purpose: Surface-language invariance for native carriers.
  A native surface is a concrete parser and linearizer over native values. The semantic object is the
  chosen native reading, not the raw surface string. When two concrete readings choose the same native
  value, the native type, denotation, evidence, and bisimilarity facts are forced to agree.
Imports: MeTTaIL.Semantics.Native, Mathlib.Order.GaloisConnection.Basic
Trusted boundary: none
Main exports: Denotational.NativeSurface, Denotational.NativeSurface.Reading,
  Denotational.NativeSurface.SameNative, Denotational.NativeEvidenceModel,
  Denotational.NativeQueryModel, Denotational.NativeConstructorView,
  Denotational.NativeGaloisBridge, Denotational.NativeGaloisBridge.searchSpec_iff_objectiveSpec
Open obligations: instantiate the surface with a real GF or MeTTaIL parser, connect constructor
  predicates to the native type checker, and connect the query/evidence layer to the world model.
-/
import MeTTaIL.Semantics.Native
import Mathlib.Order.GaloisConnection.Basic

namespace MeTTaIL
namespace Denotational

universe u v w x y z q r s a b c

/-- A concrete language surface over native semantic objects. -/
structure NativeSurface (Native : Type x) (Surface : Type r) where
  parse : Surface → Native → Prop
  linearize : Native → Surface
  linearize_sound : ∀ n, parse (linearize n) n

namespace NativeSurface

/-- A surface term together with the native object chosen for this reading. -/
structure Reading {Native : Type x} {Surface : Type r}
    (S : NativeSurface Native Surface) where
  surface : Surface
  native : Native
  parsed : S.parse surface native

/-- The reading obtained by linearizing a native object. -/
def linearized {Native : Type x} {Surface : Type r}
    (S : NativeSurface Native Surface) (n : Native) : Reading S where
  surface := S.linearize n
  native := n
  parsed := S.linearize_sound n

/-- Two concrete readings share the same native semantic object. -/
def SameNative {Native : Type x} {LeftSurface : Type r} {RightSurface : Type s}
    {L : NativeSurface Native LeftSurface} {R : NativeSurface Native RightSurface}
    (left : Reading L) (right : Reading R) : Prop :=
  left.native = right.native

namespace SameNative

/-- Same-native readings have the same native type. -/
theorem type_eq {Source : Type u} {Label : Type v} {Den : Type w}
    {SourceContext : Type z} {Native : Type x} {NativeTy : Type y}
    {NativeContext : Type q} {LeftSurface : Type r} {RightSurface : Type s}
    (N : NativeCarrier Source Label Den SourceContext Native NativeTy NativeContext)
    {L : NativeSurface Native LeftSurface} {R : NativeSurface Native RightSurface}
    {left : Reading L} {right : Reading R} (h : SameNative left right) :
    N.typeOf left.native = N.typeOf right.native :=
  congrArg N.typeOf h

/-- Same-native readings have the same denotation inherited from the carrier. -/
theorem denote_eq {Source : Type u} {Label : Type v} {Den : Type w}
    {SourceContext : Type z} {Native : Type x} {NativeTy : Type y}
    {NativeContext : Type q} {LeftSurface : Type r} {RightSurface : Type s}
    (N : NativeCarrier Source Label Den SourceContext Native NativeTy NativeContext)
    {L : NativeSurface Native LeftSurface} {R : NativeSurface Native RightSurface}
    {left : Reading L} {right : Reading R} (h : SameNative left right) :
    N.denote left.native = N.denote right.native :=
  congrArg N.denote h

/-- Same-native readings are bisimilar in the native transition system. -/
theorem bisimilar {Source : Type u} {Label : Type v} {Den : Type w}
    {SourceContext : Type z} {Native : Type x} {NativeTy : Type y}
    {NativeContext : Type q} {LeftSurface : Type r} {RightSurface : Type s}
    (N : NativeCarrier Source Label Den SourceContext Native NativeTy NativeContext)
    {L : NativeSurface Native LeftSurface} {R : NativeSurface Native RightSurface}
    {left : Reading L} {right : Reading R} (h : SameNative left right) :
    Bisimilar N.nativeLTS left.native right.native := by
  rw [← h]
  exact Bisimilar.refl N.nativeLTS left.native

/-- The inherited full-abstraction theorem applies directly to readings. -/
theorem denote_eq_iff_bisimilar {Source : Type u} {Label : Type v} {Den : Type w}
    {SourceContext : Type z} {Native : Type x} {NativeTy : Type y}
    {NativeContext : Type q} {LeftSurface : Type r} {RightSurface : Type s}
    (N : NativeCarrier Source Label Den SourceContext Native NativeTy NativeContext)
    {L : NativeSurface Native LeftSurface} {R : NativeSurface Native RightSurface}
    (left : Reading L) (right : Reading R) :
    N.denote left.native = N.denote right.native ↔
      Bisimilar N.nativeLTS left.native right.native :=
  N.eq_iff_bisimilar left.native right.native

end SameNative

end NativeSurface

/-- Evidence-valued semantics over native objects. -/
structure NativeEvidenceModel (World : Type a) (Native : Type x) (Evidence : Type b) where
  evidence : World → Native → Evidence

namespace NativeEvidenceModel

/-- Evaluate evidence at the native object chosen by a reading. -/
def evidenceOfReading {World : Type a} {Native : Type x} {Evidence : Type b}
    {Surface : Type r} (E : NativeEvidenceModel World Native Evidence) (W : World)
    {S : NativeSurface Native Surface} (reading : NativeSurface.Reading S) : Evidence :=
  E.evidence W reading.native

/-- Same-native readings have the same evidence in every world. -/
theorem evidence_eq_of_sameNative {World : Type a} {Native : Type x} {Evidence : Type b}
    {LeftSurface : Type r} {RightSurface : Type s}
    (E : NativeEvidenceModel World Native Evidence) (W : World)
    {L : NativeSurface Native LeftSurface} {R : NativeSurface Native RightSurface}
    {left : NativeSurface.Reading L} {right : NativeSurface.Reading R}
    (h : NativeSurface.SameNative left right) :
    E.evidenceOfReading W left = E.evidenceOfReading W right :=
  congrArg (E.evidence W) h

end NativeEvidenceModel

/-- Query extraction plus evidence evaluation for native objects. -/
structure NativeQueryModel (World : Type a) (Native : Type x) (Query : Type b)
    (Evidence : Type c) where
  queryOf : Native → Query
  evidence : World → Query → Evidence

namespace NativeQueryModel

/-- Evidence of a native object through its extracted query. -/
def evidenceOf {World : Type a} {Native : Type x} {Query : Type b} {Evidence : Type c}
    (M : NativeQueryModel World Native Query Evidence) (W : World) (n : Native) : Evidence :=
  M.evidence W (M.queryOf n)

/-- Same-native readings extract the same query. -/
theorem query_eq_of_sameNative {World : Type a} {Native : Type x} {Query : Type b}
    {Evidence : Type c} {LeftSurface : Type r} {RightSurface : Type s}
    (M : NativeQueryModel World Native Query Evidence)
    {L : NativeSurface Native LeftSurface} {R : NativeSurface Native RightSurface}
    {left : NativeSurface.Reading L} {right : NativeSurface.Reading R}
    (h : NativeSurface.SameNative left right) :
    M.queryOf left.native = M.queryOf right.native :=
  congrArg M.queryOf h

/-- Same-native readings have the same query-derived evidence in every world. -/
theorem evidence_eq_of_sameNative {World : Type a} {Native : Type x} {Query : Type b}
    {Evidence : Type c} {LeftSurface : Type r} {RightSurface : Type s}
    (M : NativeQueryModel World Native Query Evidence) (W : World)
    {L : NativeSurface Native LeftSurface} {R : NativeSurface Native RightSurface}
    {left : NativeSurface.Reading L} {right : NativeSurface.Reading R}
    (h : NativeSurface.SameNative left right) :
    M.evidenceOf W left.native = M.evidenceOf W right.native :=
  congrArg (M.evidenceOf W) h

end NativeQueryModel

/-- A constructor view exposes the head constructor and immediate native children. -/
structure NativeConstructorView (Native : Type x) (Constructor : Type a) where
  head : Native → Constructor
  args : Native → List Native

namespace NativeConstructorView

/-- The native predicate for values whose head constructor is `label`. -/
def constructorPredicate {Native : Type x} {Constructor : Type a}
    (V : NativeConstructorView Native Constructor) (label : Constructor) : Native → Prop :=
  fun n => V.head n = label

/-- Constructor predicates are just head-constructor equality. -/
theorem constructorPredicate_iff {Native : Type x} {Constructor : Type a}
    (V : NativeConstructorView Native Constructor) (label : Constructor) (n : Native) :
    V.constructorPredicate label n ↔ V.head n = label :=
  Iff.rfl

/-- A property is inherited from any immediate child to its parent. -/
def PreservesChildProperty {Native : Type x} {Constructor : Type a}
    (V : NativeConstructorView Native Constructor) (property : Native → Prop) : Prop :=
  ∀ {parent child}, child ∈ V.args parent → property child → property parent

end NativeConstructorView

/-- A Boolean checker whose success implies a semantic judgment. -/
structure NativeChecker (Native : Type x) (Judgment : Native → Prop) where
  check : Native → Bool
  sound : ∀ {n}, check n = true → Judgment n

namespace NativeChecker

/-- Checker soundness can be applied through a concrete reading. -/
theorem sound_of_reading {Native : Type x} {Surface : Type r} {Judgment : Native → Prop}
    (C : NativeChecker Native Judgment) {S : NativeSurface Native Surface}
    (reading : NativeSurface.Reading S) (h : C.check reading.native = true) :
    Judgment reading.native :=
  C.sound h

end NativeChecker

/-- A modal bridge given by a Galois connection. -/
structure NativeGaloisBridge (SyntaxProp : Type a) (SemanticProp : Type b)
    [Preorder SyntaxProp] [Preorder SemanticProp] where
  diamond : SyntaxProp → SemanticProp
  box : SemanticProp → SyntaxProp
  adjunction : GaloisConnection diamond box

namespace NativeGaloisBridge

/-- The exported diamond-box adjunction law. -/
theorem diamond_le_iff {SyntaxProp : Type a} {SemanticProp : Type b}
    [Preorder SyntaxProp] [Preorder SemanticProp]
    (B : NativeGaloisBridge SyntaxProp SemanticProp)
    (syntaxProp : SyntaxProp) (semanticProp : SemanticProp) :
    B.diamond syntaxProp ≤ semanticProp ↔ syntaxProp ≤ B.box semanticProp :=
  B.adjunction syntaxProp semanticProp

/-- Search-side view of a Galois specification. -/
def searchSpec {SyntaxProp : Type a} {SemanticProp : Type b}
    [Preorder SyntaxProp] [Preorder SemanticProp]
    (B : NativeGaloisBridge SyntaxProp SemanticProp)
    (syntaxProp : SyntaxProp) (semanticProp : SemanticProp) : Prop :=
  B.diamond syntaxProp ≤ semanticProp

/-- Objective-side view of the same Galois specification. -/
def objectiveSpec {SyntaxProp : Type a} {SemanticProp : Type b}
    [Preorder SyntaxProp] [Preorder SemanticProp]
    (B : NativeGaloisBridge SyntaxProp SemanticProp)
    (syntaxProp : SyntaxProp) (semanticProp : SemanticProp) : Prop :=
  syntaxProp ≤ B.box semanticProp

/-- Search and objective specifications are the two sides of the adjunction. -/
theorem searchSpec_iff_objectiveSpec {SyntaxProp : Type a} {SemanticProp : Type b}
    [Preorder SyntaxProp] [Preorder SemanticProp]
    (B : NativeGaloisBridge SyntaxProp SemanticProp)
    (syntaxProp : SyntaxProp) (semanticProp : SemanticProp) :
    B.searchSpec syntaxProp semanticProp ↔ B.objectiveSpec syntaxProp semanticProp :=
  B.diamond_le_iff syntaxProp semanticProp

/-- Unit of the Galois connection. -/
theorem le_box_diamond {SyntaxProp : Type a} {SemanticProp : Type b}
    [Preorder SyntaxProp] [Preorder SemanticProp]
    (B : NativeGaloisBridge SyntaxProp SemanticProp) (syntaxProp : SyntaxProp) :
    syntaxProp ≤ B.box (B.diamond syntaxProp) :=
  B.adjunction.le_u_l syntaxProp

/-- Counit of the Galois connection. -/
theorem diamond_box_le {SyntaxProp : Type a} {SemanticProp : Type b}
    [Preorder SyntaxProp] [Preorder SemanticProp]
    (B : NativeGaloisBridge SyntaxProp SemanticProp) (semanticProp : SemanticProp) :
    B.diamond (B.box semanticProp) ≤ semanticProp :=
  B.adjunction.l_u_le semanticProp

/-- The left adjoint is monotone. -/
theorem diamond_mono {SyntaxProp : Type a} {SemanticProp : Type b}
    [Preorder SyntaxProp] [Preorder SemanticProp]
    (B : NativeGaloisBridge SyntaxProp SemanticProp) :
    Monotone B.diamond :=
  B.adjunction.monotone_l

/-- The right adjoint is monotone. -/
theorem box_mono {SyntaxProp : Type a} {SemanticProp : Type b}
    [Preorder SyntaxProp] [Preorder SemanticProp]
    (B : NativeGaloisBridge SyntaxProp SemanticProp) :
    Monotone B.box :=
  B.adjunction.monotone_u

end NativeGaloisBridge

end Denotational
end MeTTaIL
