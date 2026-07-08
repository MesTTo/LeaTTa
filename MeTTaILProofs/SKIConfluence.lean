-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaILProofs.SKIConfluence
Layer: Proofs
Purpose: Confluence (Church-Rosser) for the SKI combinatory logic of `MeTTaIL.Calculi.SKI`. We prove
  the reflexive-transitive closure of one-step combinator reduction is confluent: if a term reduces
  in many steps to both `b` and `c`, then `b` and `c` have a common reduct. Combinatory logic is
  binder-free, so there is no substitution to manage and the argument is a structural induction by
  Tait and Martin-Lof parallel reduction in Takahashi's complete-development form. `ParRed` sits
  between `Step` and its closure and has the diamond property via the triangle for `CL.dev`, so
  Mathlib's `Relation.church_rosser` delivers Church-Rosser for `Step`. References: Takahashi,
  Parallel Reductions in lambda-Calculus (1995); Hindley, Church-Rosser for Combinatory Weak
  Reduction (1974). The Lean shape mirrors Arthur742Ramos/Metatheory, extended with the primitive
  `I` combinator.
Imports: MeTTaIL.Calculi.SKI, Mathlib
Trusted boundary: none (fully proved)
Main exports: confluence; supporting results ParRed, ParRed.triangle, ParRed.diamond, CL.dev.
Open obligations: none
-/

import MeTTaIL.Calculi.SKI
import Mathlib.Logic.Relation

namespace MeTTaIL.SKI

open Relation

/-- Many-step reduction: the reflexive-transitive closure of `Step`. -/
abbrev ReducesMany : CL → CL → Prop := ReflTransGen Step

/-! ## Parallel reduction

`ParRed a b` contracts zero or more redexes of `a` simultaneously. The atoms reduce only to
themselves, application is a congruence, and each combinator rule may fire with its arguments
reduced in parallel. General reflexivity is derived below. -/

/-- Parallel reduction: contract any number of redexes in a single step. -/
inductive ParRed : CL → CL → Prop where
  | S : ParRed .S .S
  | K : ParRed .K .K
  | I : ParRed .I .I
  | app {a a' b b'} : ParRed a a' → ParRed b b' → ParRed (.app a b) (.app a' b')
  | kp {x x' y y'} : ParRed x x' → ParRed y y' → ParRed (.app (.app .K x) y) x'
  | sp {x x' y y' z z'} : ParRed x x' → ParRed y y' → ParRed z z' →
      ParRed (.app (.app (.app .S x) y) z) (.app (.app x' z') (.app y' z'))
  | ip {x x'} : ParRed x x' → ParRed (.app .I x) x'

namespace ParRed

/-- Parallel reduction is reflexive. -/
theorem refl : ∀ a : CL, ParRed a a
  | .S => .S
  | .K => .K
  | .I => .I
  | .app a b => .app (refl a) (refl b)

/-- A single reduction step is a parallel step. -/
theorem ofStep {a b : CL} (h : Step a b) : ParRed a b := by
  induction h with
  | k => exact .kp (refl _) (refl _)
  | s => exact .sp (refl _) (refl _) (refl _)
  | i => exact .ip (refl _)
  | appL _ ih => exact .app ih (refl _)
  | appR _ ih => exact .app (refl _) ih

/-- Many-step reduction is a congruence on the left of an application. -/
theorem reducesMany_appL {a a' b : CL} (h : ReducesMany a a') :
    ReducesMany (.app a b) (.app a' b) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (.appL hst)

/-- Many-step reduction is a congruence on the right of an application. -/
theorem reducesMany_appR {a b b' : CL} (h : ReducesMany b b') :
    ReducesMany (.app a b) (.app a b') := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (.appR hst)

/-- Many-step reduction is a congruence on applications. -/
theorem reducesMany_app {a a' b b' : CL} (ha : ReducesMany a a') (hb : ReducesMany b b') :
    ReducesMany (.app a b) (.app a' b') :=
  (reducesMany_appL ha).trans (reducesMany_appR hb)

/-- A parallel step is realized by finitely many single steps. -/
theorem toReducesMany {a b : CL} (h : ParRed a b) : ReducesMany a b := by
  induction h with
  | S => exact .refl
  | K => exact .refl
  | I => exact .refl
  | app _ _ iha ihb => exact reducesMany_app iha ihb
  | @kp x x' y y' _ _ ihx _ =>
      -- (K x y) -> x -> x'
      exact (ReflTransGen.single Step.k).trans ihx
  | @sp x x' y y' z z' _ _ _ ihx ihy ihz =>
      -- (S x y z) -> (x z) (y z) ->* (x' z') (y' z')
      exact (ReflTransGen.single Step.s).trans (reducesMany_app (reducesMany_app ihx ihz)
        (reducesMany_app ihy ihz))
  | @ip x x' _ ihx =>
      -- (I x) -> x -> x'
      exact (ReflTransGen.single Step.i).trans ihx

end ParRed

/-! ## Complete development

`CL.dev a` contracts every redex of `a` in one pass. Reading the equations: a `K`-redex drops its
second argument, an `S`-redex distributes, an `I`-redex strips the head, and otherwise the
development recurses into both sides of an application. -/

/-- The complete development: contract all redexes of a term simultaneously. -/
def CL.dev : CL → CL
  | .S => .S
  | .K => .K
  | .I => .I
  | .app (.app .K x) _ => CL.dev x
  | .app (.app (.app .S x) y) z => .app (.app (CL.dev x) (CL.dev z)) (.app (CL.dev y) (CL.dev z))
  | .app .I x => CL.dev x
  | .app a b => .app (CL.dev a) (CL.dev b)

namespace ParRed

/-! ### Inversion lemmas for the triangle

To prove the triangle we case on the head of an application redex. These lemmas read off the shape
of the reduct of a partially applied combinator, which is forced because such terms have no redex
of their own. -/

/-- A reduct of `K x` is `K x'` with `x ⇒ x'`. -/
theorem inv_Kx {x t : CL} (h : ParRed (.app .K x) t) :
    ∃ x', t = .app .K x' ∧ ParRed x x' := by
  cases h with
  | app hK hx => cases hK; exact ⟨_, rfl, hx⟩

/-- A reduct of `S x` is `S x'` with `x ⇒ x'`. -/
theorem inv_Sx {x t : CL} (h : ParRed (.app .S x) t) :
    ∃ x', t = .app .S x' ∧ ParRed x x' := by
  cases h with
  | app hS hx => cases hS; exact ⟨_, rfl, hx⟩

/-- A reduct of `S x y` is `S x' y'` with `x ⇒ x'` and `y ⇒ y'`. -/
theorem inv_Sxy {x y t : CL} (h : ParRed (.app (.app .S x) y) t) :
    ∃ x' y', t = .app (.app .S x') y' ∧ ParRed x x' ∧ ParRed y y' := by
  cases h with
  | app hSx hy =>
      obtain ⟨x', rfl, hx⟩ := inv_Sx hSx
      exact ⟨x', _, rfl, hx, hy⟩

/-- The triangle: every parallel reduct of `a` reduces to the complete development `CL.dev a`.
    This is the engine of confluence; the diamond follows by taking `CL.dev a` as the common
    reduct. -/
theorem triangle {a b : CL} (h : ParRed a b) : ParRed b (CL.dev a) := by
  induction h with
  | S => exact .S
  | K => exact .K
  | I => exact .I
  | @app a a' bb b' hM hN ihM ihN =>
      -- `app a' b' ⇒ CL.dev (app a bb)`. Case on the head `a`. The whole application is a redex
      -- exactly when `a` is `I` (an `I`-redex), `K x` (a `K`-redex), or `S x y` (an `S`-redex);
      -- in every other shape `CL.dev` recurses into both sides and the congruence `app` closes it.
      -- Revert the hypotheses that mention `a` so the match refines them together with the goal.
      revert hM ihM
      match a with
      | .S => intro _ ihM; exact .app ihM ihN
      | .K => intro _ ihM; exact .app ihM ihN
      | .I =>
          -- `app I bb` is an I-redex: `CL.dev (app I bb) = CL.dev bb`.
          intro hM _; cases hM; exact .ip ihN
      | .app .K x =>
          -- `app (app K x) bb` is a K-redex: `CL.dev = CL.dev x`.
          intro hM ihM
          obtain ⟨x', rfl, _⟩ := inv_Kx hM
          obtain ⟨x'', e, hx''⟩ := inv_Kx ihM
          obtain rfl : x'' = CL.dev x := by cases e; rfl
          exact .kp hx'' ihN
      | .app .S x =>
          -- `app (app S x) bb` is a partial S (two args), not a redex.
          intro hM ihM
          obtain ⟨x', rfl, _⟩ := inv_Sx hM
          exact .app ihM ihN
      | .app .I x =>
          -- `app (app I x) bb`: the inner `app I x` is an I-redex, but the top is plain app.
          intro _ ihM; exact .app ihM ihN
      | .app (.app .K x) y =>
          -- `app (app (app K x) y) bb`: the inner `app (app K x) y` is the K-redex; top is app.
          intro _ ihM; exact .app ihM ihN
      | .app (.app .S x) y =>
          -- `app (app (app S x) y) bb` is an S-redex.
          intro hM ihM
          obtain ⟨x', y', rfl, _, _⟩ := inv_Sxy hM
          -- `ihM : app (app S x') y' ⇒ CL.dev (app (app S x) y) = app (app S (dev x)) (dev y)`.
          obtain ⟨x'', y'', e, hx'', hy''⟩ := inv_Sxy ihM
          obtain ⟨rfl, rfl⟩ : x'' = CL.dev x ∧ y'' = CL.dev y := by cases e; exact ⟨rfl, rfl⟩
          exact .sp hx'' hy'' ihN
      | .app (.app .I x) y =>
          intro _ ihM; exact .app ihM ihN
      | .app (.app (.app f g) x) y =>
          intro _ ihM; exact .app ihM ihN
  | @kp x x' y y' hx _ ihx _ =>
      -- `CL.dev (app (app K x) y) = CL.dev x`, and `ihx : x' ⇒ CL.dev x`.
      exact ihx
  | @sp x x' y y' z z' _ _ _ ihx ihy ihz =>
      -- `CL.dev (app (app (app S x) y) z) = (dev x dev z)(dev y dev z)`.
      exact .app (.app ihx ihz) (.app ihy ihz)
  | @ip x x' _ ihx =>
      -- `CL.dev (app I x) = CL.dev x`, and `ihx : x' ⇒ CL.dev x`.
      exact ihx

/-- The diamond property for parallel reduction: two parallel reducts of a term share a further
    reduct, namely the complete development. -/
theorem diamond {a b c : CL} (hb : ParRed a b) (hc : ParRed a c) :
    ∃ d, ParRed b d ∧ ParRed c d :=
  ⟨CL.dev a, triangle hb, triangle hc⟩

end ParRed

/-! ## Confluence

The closures of `Step` and `ParRed` agree, and `ParRed` has the diamond, so the reflexive-transitive
closure of `Step` is Church-Rosser. -/

/-- A many-step `Step` reduction is a many-step `ParRed` reduction (since `Step ⊆ ParRed`). -/
theorem reducesMany_toParRedStar {a b : CL} (h : ReducesMany a b) :
    ReflTransGen ParRed a b :=
  ReflTransGen.mono (fun _ _ hs => ParRed.ofStep hs) h

/-- A many-step `ParRed` reduction is a many-step `Step` reduction (since each parallel step is a
    finite sequence of single steps). -/
theorem parRedStar_toReducesMany {a b : CL} (h : ReflTransGen ParRed a b) :
    ReducesMany a b := by
  induction h with
  | refl => exact .refl
  | tail _ hp ih => exact ih.trans hp.toReducesMany

/-- Confluence (Church-Rosser) for SKI combinatory logic: any two many-step reducts of a common
    term have a common reduct. -/
theorem confluence {a b c : CL} (hb : ReducesMany a b) (hc : ReducesMany a c) :
    ∃ d, ReducesMany b d ∧ ReducesMany c d := by
  have hcr : Join (ReflTransGen ParRed) b c :=
    church_rosser
      (fun _ x y hx hy =>
        let ⟨d, hxd, hyd⟩ := ParRed.diamond hx hy
        ⟨d, .single hxd, .single hyd⟩)
      (reducesMany_toParRedStar hb) (reducesMany_toParRedStar hc)
  obtain ⟨d, hbd, hcd⟩ := hcr
  exact ⟨d, parRedStar_toReducesMany hbd, parRedStar_toReducesMany hcd⟩

end MeTTaIL.SKI
