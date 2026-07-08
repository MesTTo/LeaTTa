-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Calculi.SKI
Layer: Calculi
Purpose: SKI combinatory logic, the binder-free combinatory calculus. `hypercube.md` gives a GSLT
  presentation of it through intermediate combinators (`S1`, `S2`, `K1`) and six named one-step rules;
  here the standard direct `S`/`K`/`I` rules with congruence are used, which is the same calculus by a
  different presentation. The file proves a concrete subject-reduction (preservation) result for the
  kind of typed discipline a GSLT's hypercube aims to provide. Because combinatory logic has no
  variables or binders, typing and reduction are first-order and subject reduction is a structural
  induction with no substitution machinery. `Step` is the combinator reduction (S, K, I rules plus
  congruence), `HasTy` is the standard simply-typed combinatory-logic system, and `preservation` is
  subject reduction.
Imports: none (Mathlib-free)
Trusted boundary: human-reviewed spec
Main exports: CL, Ty, Step, HasTy, preservation
Open obligations: the full modal hypercube typing for binder calculi (the RHO calculus) is left open by
  the source notes; the determinate, binder-free case is what is proved here.
-/

namespace MeTTaIL.SKI

/-- Combinatory-logic terms: the three primitive combinators and application. -/
inductive CL where
  | S | K | I
  | app (fn arg : CL)
deriving Repr, DecidableEq, Inhabited

/-- Simple types: base types and function types. -/
inductive Ty where
  | base (n : Nat)
  | arr (dom cod : Ty)
deriving Repr, DecidableEq, Inhabited

/-- One-step combinator reduction. The three combinator rules, plus congruence in either side of an
    application. -/
inductive Step : CL → CL → Prop where
  | k {x y} : Step (.app (.app .K x) y) x
  | s {x y z} : Step (.app (.app (.app .S x) y) z) (.app (.app x z) (.app y z))
  | i {x} : Step (.app .I x) x
  | appL {a a' b} : Step a a' → Step (.app a b) (.app a' b)
  | appR {a b b'} : Step b b' → Step (.app a b) (.app a b')

/-- The simply-typed combinatory-logic typing relation. The combinator constants have their usual
    principal types; application is the standard arrow elimination. -/
inductive HasTy : CL → Ty → Prop where
  | tI {a} : HasTy .I (.arr a a)
  | tK {a b} : HasTy .K (.arr a (.arr b a))
  | tS {a b c} : HasTy .S (.arr (.arr a (.arr b c)) (.arr (.arr a b) (.arr a c)))
  | tApp {a b f x} : HasTy f (.arr a b) → HasTy x a → HasTy (.app f x) b

/-- Subject reduction (type preservation): reduction preserves typing. -/
theorem preservation {t t' : CL} (hs : Step t t') : ∀ {τ : Ty}, HasTy t τ → HasTy t' τ := by
  induction hs with
  | k =>
      intro _ ht
      cases ht with
      | tApp hKx hy => cases hKx with | tApp hK hx => cases hK; exact hx
  | s =>
      intro _ ht
      cases ht with
      | tApp hSxy hz =>
          cases hSxy with
          | tApp hSx hy =>
              cases hSx with
              | tApp hS hx => cases hS; exact .tApp (.tApp hx hz) (.tApp hy hz)
  | i =>
      intro _ ht
      cases ht with
      | tApp hI hx => cases hI; exact hx
  | appL _ ih =>
      intro _ ht
      cases ht with
      | tApp hf hx => exact .tApp (ih hf) hx
  | appR _ ih =>
      intro _ ht
      cases ht with
      | tApp hf hx => exact .tApp hf (ih hx)

/-- `K I I` reduces to `I` (the second argument is discarded). -/
example : Step (.app (.app .K .I) .I) .I := .k

/-- `K I I` is well typed at `b0 -> b0`: `K` keeps the first identity and discards the second. -/
example : HasTy (.app (.app .K .I) .I) (.arr (.base 0) (.base 0)) :=
  .tApp (.tApp .tK .tI) (.tI (a := .base 1))

/-- Subject reduction in action: the reduct `I` keeps the type `b0 -> b0`. -/
example (ht : HasTy (.app (.app .K .I) .I) (.arr (.base 0) (.base 0))) :
    HasTy .I (.arr (.base 0) (.base 0)) :=
  preservation .k ht

end MeTTaIL.SKI
