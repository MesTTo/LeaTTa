-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaILProofs.DistributiveLaw
Layer: Proofs
Purpose: Beck's theorem that a distributive law of two monads yields a composite monad, stated and
  proved generically for `CategoryTheory.Monad C` over an arbitrary category `C`. This is the general
  (non-thin) 2-categorical content, monads in the 2-category `Cat`, which generalizes the thin/poset
  closure-operator case `composeClosure` in `MeTTaILProofs.OSLFCat.lean` (where the 2-category is a
  partial order and monads are closure operators). The references are Jon Beck, "Distributive laws",
  in Seminar on Triples and Categorical Homology Theory, LNM 80, Springer 1969, and Ross Street, "The
  formal theory of monads", J. Pure Appl. Algebra 2 (1972).

  A distributive law of `S` over `T` is a natural transformation `δ : S ⋙ T ⟶ T ⋙ S` satisfying four
  axioms, two about the units and two about the multiplications. From such a `δ` we build a monad on
  the composite functor `T ⋙ S` whose unit is the horizontal composite of the two units and whose
  multiplication uses `δ` whiskered on both sides followed by the two multiplications. We then prove
  the three monad laws and package the result as `composeMonad`.

  Orientation convention. Mathlib's `⋙` applies the left functor first, so `(S ⋙ T).obj X` is
  `T.obj (S.obj X)`, classically `T ∘ S`. We take `δ : S ⋙ T ⟶ T ⋙ S`, classically `δ : T S ⟹ S T`,
  and build the composite monad on `T ⋙ S`, whose object map is `S.obj (T.obj X)`, classically the
  composite `S ∘ T`. So the headline composite is the classical `S ∘ T` monad. All four axioms and the
  composite multiplication below are pinned down by making the Mathlib whiskering and composition
  types check; the per-object content matches the standard Beck axioms.

Imports: Mathlib.CategoryTheory.Monad.Basic (the `Monad` structure, its laws, and the identity monad),
  Mathlib.CategoryTheory.Whiskering (`whiskerLeft`, `whiskerRight`, and their component lemmas)
Trusted boundary: none (fully proved, no axioms beyond Mathlib's `propext`, `Classical.choice`,
  `Quot.sound`)
Main exports: DistributiveLaw, composeMonad (Beck's theorem), idLaw (the trivial distributive law of a
  monad over the identity monad, witnessing non-vacuity)
-/
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Whiskering

namespace MeTTaIL.Beck

open CategoryTheory Category Functor

universe v u

variable {C : Type u} [Category.{v} C]

/-! ### Distributive laws

A distributive law of the monad `S` over the monad `T` is a natural transformation
`δ : S ⋙ T ⟶ T ⋙ S` compatible with the units and multiplications of both monads. The four fields
below are the standard Beck axioms, written with Mathlib's `whiskerLeft` and `whiskerRight`. Two
control the interaction with the units `S.η` and `T.η`, and two control the interaction with the
multiplications `S.μ` and `T.μ`. -/

/-- A distributive law of `S` over `T`: a natural transformation `δ : S ⋙ T ⟶ T ⋙ S` satisfying the
four Beck axioms. -/
structure DistributiveLaw (S T : Monad C) where
  /-- The distributing natural transformation. -/
  δ : (S : C ⥤ C) ⋙ (T : C ⥤ C) ⟶ (T : C ⥤ C) ⋙ (S : C ⥤ C)
  /-- Compatibility with the unit of `S`. -/
  unit_S : whiskerRight S.η (T : C ⥤ C) ≫ δ = whiskerLeft (T : C ⥤ C) S.η := by cat_disch
  /-- Compatibility with the unit of `T`. -/
  unit_T : whiskerLeft (S : C ⥤ C) T.η ≫ δ = whiskerRight T.η (S : C ⥤ C) := by cat_disch
  /-- Compatibility with the multiplication of `S`. -/
  mult_S : whiskerRight S.μ (T : C ⥤ C) ≫ δ =
    whiskerLeft (S : C ⥤ C) δ ≫ whiskerRight δ (S : C ⥤ C) ≫ whiskerLeft (T : C ⥤ C) S.μ := by
      cat_disch
  /-- Compatibility with the multiplication of `T`. -/
  mult_T : whiskerLeft (S : C ⥤ C) T.μ ≫ δ =
    whiskerRight δ (T : C ⥤ C) ≫ whiskerLeft (T : C ⥤ C) δ ≫ whiskerRight T.μ (S : C ⥤ C) := by
      cat_disch

namespace DistributiveLaw

variable {S T : Monad C} (l : DistributiveLaw S T)

/-! ### The four axioms, per object

The structure fields are equalities of natural transformations. For the diagram chases that prove the
monad laws we use the per-object form of each axiom, extracted by `NatTrans.congr_app`. -/

/-- Per-object form of `unit_S`. -/
@[reassoc]
theorem unit_S_app (X : C) :
    (T : C ⥤ C).map (S.η.app X) ≫ l.δ.app X = S.η.app ((T : C ⥤ C).obj X) :=
  NatTrans.congr_app l.unit_S X

/-- Per-object form of `unit_T`. -/
@[reassoc]
theorem unit_T_app (X : C) :
    T.η.app ((S : C ⥤ C).obj X) ≫ l.δ.app X = (S : C ⥤ C).map (T.η.app X) :=
  NatTrans.congr_app l.unit_T X

/-- Per-object form of `mult_S`. -/
@[reassoc]
theorem mult_S_app (X : C) :
    (T : C ⥤ C).map (S.μ.app X) ≫ l.δ.app X =
      l.δ.app ((S : C ⥤ C).obj X) ≫ (S : C ⥤ C).map (l.δ.app X) ≫ S.μ.app ((T : C ⥤ C).obj X) :=
  NatTrans.congr_app l.mult_S X

/-- Per-object form of `mult_T`. -/
@[reassoc]
theorem mult_T_app (X : C) :
    T.μ.app ((S : C ⥤ C).obj X) ≫ l.δ.app X =
      (T : C ⥤ C).map (l.δ.app X) ≫ l.δ.app ((T : C ⥤ C).obj X) ≫ (S : C ⥤ C).map (T.μ.app X) :=
  NatTrans.congr_app l.mult_T X

/-- The `unit_S` axiom transported under `S.map` (the form that appears in the composite multiplication,
    where `δ` is whiskered by `S`). -/
@[reassoc]
theorem map_unit_S (X : C) :
    (S : C ⥤ C).map ((T : C ⥤ C).map (S.η.app X)) ≫ (S : C ⥤ C).map (l.δ.app X) =
      (S : C ⥤ C).map (S.η.app ((T : C ⥤ C).obj X)) := by
  rw [← Functor.map_comp]; exact congrArg (S : C ⥤ C).map (l.unit_S_app X)

/-- The `mult_S` axiom transported under `S.map`. -/
@[reassoc]
theorem map_mult_S (X : C) :
    (S : C ⥤ C).map ((T : C ⥤ C).map (S.μ.app X)) ≫ (S : C ⥤ C).map (l.δ.app X) =
      (S : C ⥤ C).map (l.δ.app ((S : C ⥤ C).obj X)) ≫
        (S : C ⥤ C).map ((S : C ⥤ C).map (l.δ.app X)) ≫ (S : C ⥤ C).map (S.μ.app ((T : C ⥤ C).obj X)) := by
  simp only [← Functor.map_comp]; exact congrArg (S : C ⥤ C).map (l.mult_S_app X)

/-! ### The composite monad

With `δ : S ⋙ T ⟶ T ⋙ S` we build a monad on `T ⋙ S`. The unit is `T.η` followed by `S.η` whiskered
by `T`, so at `X` it is `T.η X ≫ S.η (T X)`. The multiplication whiskers `δ` by `T` on the left and by
`S` on the right, then applies `S.μ` and `T.μ`, so at `X` it is
`S (δ (T X)) ≫ S.μ (T (T X)) ≫ S (T.μ X)`. Both are assembled from whiskers and composition, so their
naturality is inherited. -/

/-- The unit of the composite monad, `𝟭 C ⟶ T ⋙ S`. -/
def composeη : 𝟭 C ⟶ (T : C ⥤ C) ⋙ (S : C ⥤ C) :=
  T.η ≫ whiskerLeft (T : C ⥤ C) S.η

/-- The multiplication of the composite monad, `(T ⋙ S) ⋙ (T ⋙ S) ⟶ T ⋙ S`. -/
def composeμ :
    ((T : C ⥤ C) ⋙ (S : C ⥤ C)) ⋙ ((T : C ⥤ C) ⋙ (S : C ⥤ C)) ⟶ (T : C ⥤ C) ⋙ (S : C ⥤ C) :=
  whiskerRight (whiskerLeft (T : C ⥤ C) l.δ) (S : C ⥤ C) ≫
    whiskerLeft ((T : C ⥤ C) ⋙ (T : C ⥤ C)) S.μ ≫
    whiskerRight T.μ (S : C ⥤ C)

/-- Per-object form of the composite unit. -/
theorem composeη_app (X : C) :
    (composeη (S := S) (T := T)).app X = T.η.app X ≫ S.η.app ((T : C ⥤ C).obj X) :=
  rfl

/-- Per-object form of the composite multiplication. -/
theorem composeμ_app (X : C) :
    (l.composeμ).app X =
      (S : C ⥤ C).map (l.δ.app ((T : C ⥤ C).obj X)) ≫
        S.μ.app ((T : C ⥤ C).obj ((T : C ⥤ C).obj X)) ≫ (S : C ⥤ C).map (T.μ.app X) :=
  rfl

/-- Beck's theorem: a distributive law of `S` over `T` yields a monad on the composite functor
`T ⋙ S`, classically the monad `S ∘ T`. -/
def composeMonad : Monad C where
  toFunctor := (T : C ⥤ C) ⋙ (S : C ⥤ C)
  η := composeη
  μ := l.composeμ
  assoc := by
    intro X
    simp only [composeμ, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      Functor.comp_map, Functor.map_comp, Category.assoc]
    -- LHS step 1: δ-naturality (under S) at the S(T(S(n_X))) ≫ S(d_{TX}) junction.
    have S1 : (S : C ⥤ C).map ((T : C ⥤ C).map ((S : C ⥤ C).map (T.μ.app X))) ≫
        (S : C ⥤ C).map (l.δ.app ((T : C ⥤ C).obj X)) =
        (S : C ⥤ C).map (l.δ.app ((T : C ⥤ C).obj ((T : C ⥤ C).obj X))) ≫
          (S : C ⥤ C).map ((S : C ⥤ C).map ((T : C ⥤ C).map (T.μ.app X))) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (S : C ⥤ C).map (l.δ.naturality (T.μ.app X))
    -- LHS step 3: mult_S (under S) at the S(T(m_{T²X})) ≫ S(d_{T²X}) junction.
    have S3 : (S : C ⥤ C).map ((T : C ⥤ C).map (S.μ.app ((T : C ⥤ C).obj ((T : C ⥤ C).obj X)))) ≫
        (S : C ⥤ C).map (l.δ.app ((T : C ⥤ C).obj ((T : C ⥤ C).obj X))) =
        (S : C ⥤ C).map (l.δ.app ((S : C ⥤ C).obj ((T : C ⥤ C).obj ((T : C ⥤ C).obj X)))) ≫
          (S : C ⥤ C).map ((S : C ⥤ C).map (l.δ.app ((T : C ⥤ C).obj ((T : C ⥤ C).obj X)))) ≫
            (S : C ⥤ C).map (S.μ.app ((T : C ⥤ C).obj ((T : C ⥤ C).obj ((T : C ⥤ C).obj X)))) := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (S : C ⥤ C).map (l.mult_S_app ((T : C ⥤ C).obj ((T : C ⥤ C).obj X)))
    -- LHS step 6: T-monad associativity (under S) at the S(T(n_X)) ≫ S(n_X) junction.
    have S6 : (S : C ⥤ C).map ((T : C ⥤ C).map (T.μ.app X)) ≫ (S : C ⥤ C).map (T.μ.app X) =
        (S : C ⥤ C).map (T.μ.app ((T : C ⥤ C).obj X)) ≫ (S : C ⥤ C).map (T.μ.app X) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (S : C ⥤ C).map (T.assoc X)
    -- RHS step 1: mult_T (under S) at the S(n_{STX}) ≫ S(d_{TX}) junction.
    have R1 : (S : C ⥤ C).map (T.μ.app ((S : C ⥤ C).obj ((T : C ⥤ C).obj X))) ≫
        (S : C ⥤ C).map (l.δ.app ((T : C ⥤ C).obj X)) =
        (S : C ⥤ C).map ((T : C ⥤ C).map (l.δ.app ((T : C ⥤ C).obj X))) ≫
          (S : C ⥤ C).map (l.δ.app ((T : C ⥤ C).obj ((T : C ⥤ C).obj X))) ≫
            (S : C ⥤ C).map ((S : C ⥤ C).map (T.μ.app ((T : C ⥤ C).obj X))) := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (S : C ⥤ C).map (l.mult_T_app ((T : C ⥤ C).obj X))
    -- RHS step 3: δ-naturality (under S) at the S(d_{T(STX)}) ≫ S(S(T(d_{TX}))) junction.
    have R3 : (S : C ⥤ C).map (l.δ.app ((T : C ⥤ C).obj ((S : C ⥤ C).obj ((T : C ⥤ C).obj X)))) ≫
        (S : C ⥤ C).map ((S : C ⥤ C).map ((T : C ⥤ C).map (l.δ.app ((T : C ⥤ C).obj X)))) =
        (S : C ⥤ C).map ((T : C ⥤ C).map ((S : C ⥤ C).map (l.δ.app ((T : C ⥤ C).obj X)))) ≫
          (S : C ⥤ C).map (l.δ.app ((S : C ⥤ C).obj ((T : C ⥤ C).obj ((T : C ⥤ C).obj X)))) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (S : C ⥤ C).map ((l.δ.naturality (l.δ.app ((T : C ⥤ C).obj X))).symm)
    -- Top-level S.μ-naturality and S-monad associativity used on both sides.
    have S2 := S.μ.naturality ((T : C ⥤ C).map (T.μ.app X))
    have S4 := S.assoc ((T : C ⥤ C).obj ((T : C ⥤ C).obj ((T : C ⥤ C).obj X)))
    have S5 := S.μ.naturality (l.δ.app ((T : C ⥤ C).obj ((T : C ⥤ C).obj X)))
    have R2 := (S.μ.naturality ((T : C ⥤ C).map (l.δ.app ((T : C ⥤ C).obj X)))).symm
    have R4 := S.μ.naturality (T.μ.app ((T : C ⥤ C).obj X))
    erw [Category.assoc, Category.assoc]
    erw [reassoc_of% S1, Category.assoc, reassoc_of% S2]
    erw [reassoc_of% S3, Category.assoc, Category.assoc, reassoc_of% S4]
    erw [Category.assoc, reassoc_of% S5, S6]
    erw [reassoc_of% R1, Category.assoc, reassoc_of% R2]
    erw [reassoc_of% R3, Category.assoc, Category.assoc, reassoc_of% R4]
    rfl
  left_unit := by
    intro X
    simp only [composeμ, composeη, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      Functor.id_obj, Category.assoc]
    erw [← S.η.naturality_assoc, l.unit_T_app_assoc, S.left_unit_assoc, ← Functor.map_comp,
      T.left_unit, Functor.map_id]
    rfl
  right_unit := by
    intro X
    simp only [composeμ, composeη, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      Functor.comp_map, Functor.id_obj, Functor.map_comp]
    erw [Category.assoc, l.map_unit_S_assoc, S.right_unit_assoc, ← Functor.map_comp, T.right_unit,
      Functor.map_id]
    rfl

/-! ### Non-vacuity

The structure is inhabited. For any monad `S` there is a distributive law of `S` over the identity
monad, with `δ` the identity natural transformation. Feeding it to `composeMonad` builds a genuine
monad, so the construction is not vacuous. -/

/-- The trivial distributive law of any monad `S` over the identity monad, with `δ = 𝟙`. -/
def idLaw (S : Monad C) : DistributiveLaw S (Monad.id C) where
  δ := 𝟙 _
  unit_S := by
    ext X
    simp only [whiskerRight_app, whiskerLeft_app, NatTrans.comp_app, NatTrans.id_app, Monad.id]
    erw [Category.comp_id]; rfl
  unit_T := by
    ext X
    simp only [whiskerRight_app, whiskerLeft_app, NatTrans.comp_app, NatTrans.id_app, Monad.id]
    erw [Category.id_comp, Functor.map_id]; rfl
  mult_S := by
    ext X
    simp only [whiskerRight_app, whiskerLeft_app, NatTrans.comp_app, NatTrans.id_app, Monad.id]
    erw [Category.comp_id, Functor.map_id, Category.id_comp, Category.id_comp]; rfl
  mult_T := by
    ext X
    simp only [whiskerRight_app, whiskerLeft_app, NatTrans.comp_app, NatTrans.id_app, Monad.id]
    erw [Functor.map_id, Functor.map_id, Category.id_comp, Category.id_comp]

/-- Non-vacuity: `composeMonad` produces an actual monad from the identity distributive law. -/
example (S : Monad C) : Monad C := (idLaw S).composeMonad

end DistributiveLaw

end MeTTaIL.Beck

-- Axiom audit: confirms the composite monad depends only on Mathlib's standard axioms.
