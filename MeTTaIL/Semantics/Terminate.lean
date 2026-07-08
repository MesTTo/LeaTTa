-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Semantics.Terminate
Layer: Semantics
Purpose: Conditional termination of the runtime. If a measure `μ` strictly decreases on every rewrite
  step, the rewrite system terminates, and the fuel-bounded normalizer reaches a normal form within
  `μ t` fuel. `eval_reaches_normal` is the bound, and `eval_computes_normal_of_measure` packages it with
  soundness: under a decreasing measure the runtime computes a normal form that the input genuinely
  rewrites to. This is the termination half of Maude's executability conditions; a measure is exactly a
  termination proof of the presentation's rewrite system.
Imports: MeTTaIL.Semantics.Normal
Trusted boundary: none (fully proved)
Main exports: eval_reaches_normal, eval_normal_of_measure, eval_computes_normal_of_measure
Open obligations: confluence (uniqueness of the normal form) and discharging the measure hypothesis by
  an automatic termination criterion are future work.
-/
import MeTTaIL.Semantics.Normal

namespace MeTTaIL

/-- With a measure that strictly decreases on every step, `μ t` fuel suffices to reach a normal form.
    Proved by induction on the fuel bound, using that a step from a measure-zero term is impossible. -/
theorem eval_reaches_normal (p : Presentation) (μ : AST → Nat)
    (hμ : ∀ t t', RewStep p t t' → μ t' < μ t) :
    ∀ (n : Nat) (t : AST), μ t ≤ n → IsNormal p (eval p n t)
  | 0, t, hn => by
      have hnone : oneStep p t = none := by
        cases hs : oneStep p t with
        | none => rfl
        | some t' => exact absurd (hμ t t' (oneStep_sound p t hs)) (by omega)
      simpa [eval, IsNormal] using hnone
  | n + 1, t, hn => by
      cases hs : oneStep p t with
      | none =>
          have he : eval p (n + 1) t = t := by simp [eval, hs]
          rw [he]; exact hs
      | some t' =>
          have hlt : μ t' < μ t := hμ t t' (oneStep_sound p t hs)
          have he : eval p (n + 1) t = eval p n t' := by simp [eval, hs]
          rw [he]
          exact eval_reaches_normal p μ hμ n t' (by omega)

/-- Under a strictly decreasing measure, the normalizer reaches a normal form with `μ t` fuel. -/
theorem eval_normal_of_measure (p : Presentation) (μ : AST → Nat)
    (hμ : ∀ t t', RewStep p t t' → μ t' < μ t) (t : AST) :
    IsNormal p (eval p (μ t) t) :=
  eval_reaches_normal p μ hμ (μ t) t (Nat.le_refl _)

/-- The runtime computes a normal form: under a decreasing measure, `eval p (μ t) t` is reachable from
    `t` by the presentation's rewrites and is itself normal. -/
theorem eval_computes_normal_of_measure (p : Presentation) (μ : AST → Nat)
    (hμ : ∀ t t', RewStep p t t' → μ t' < μ t) (t : AST) :
    RewStepMany p t (eval p (μ t) t) ∧ IsNormal p (eval p (μ t) t) :=
  ⟨eval_sound p (μ t) t, eval_normal_of_measure p μ hμ t⟩

end MeTTaIL
