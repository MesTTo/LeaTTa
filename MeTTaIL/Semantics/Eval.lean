-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Semantics.Eval
Layer: Semantics
Purpose: The fuel-bounded normalizer that turns the one-step reducer into a runtime. `eval` applies
  `oneStep` until no step applies or the fuel runs out; it is total, with no `partial`. The headline is
  `eval_sound`: the normalizer's result is always reachable from the input by many context rewrites,
  so every run is a genuine reduction sequence of the presentation. `eval_fixed_of_normal` records that
  a normal term is a fixpoint. Detecting "stopped because normal rather than out of fuel" is decidable
  via `IsNormal` (whether `oneStep` of the result is `none`); a full completeness statement (that
  reaching `none` means no reduction exists) is strategy-dependent and deferred to the confluence and
  strategy stage.
Imports: MeTTaIL.Semantics.Context
Trusted boundary: none (fully proved)
Main exports: RewStepMany, RewStepMany.single, RewStepMany.trans, eval, IsNormal, eval_sound,
  eval_fixed_of_normal
Open obligations: completeness (that the normalizer finds a normal form whenever one exists) needs a
  normalizing strategy (parallel-outermost) and is future work.
-/
import MeTTaIL.Semantics.Context

namespace MeTTaIL

/-- Many-step context rewriting: the reflexive-transitive closure of `RewStep`. -/
inductive RewStepMany (p : Presentation) : AST → AST → Prop where
  | refl {t : AST} : RewStepMany p t t
  | tail {t u v : AST} : RewStepMany p t u → RewStep p u v → RewStepMany p t v

/-- A single step is a many-step. -/
theorem RewStepMany.single {p : Presentation} {t t' : AST} (h : RewStep p t t') :
    RewStepMany p t t' := .tail .refl h

/-- Many-step rewriting composes. -/
theorem RewStepMany.trans {p : Presentation} {t u v : AST}
    (h₁ : RewStepMany p t u) (h₂ : RewStepMany p u v) : RewStepMany p t v := by
  induction h₂ with
  | refl => exact h₁
  | tail _ s ih => exact .tail ih s

/-- The fuel-bounded normalizer: apply `oneStep` until no step applies or the fuel runs out. Total,
    no `partial`; the fuel makes the driver structurally recursive even when reduction may not
    terminate. -/
def eval (p : Presentation) : Nat → AST → AST
  | 0, t => t
  | fuel + 1, t =>
      match oneStep p t with
      | some t' => eval p fuel t'
      | none => t

/-- A term is normal when no one-step reduction applies. Decidable, since `oneStep` is computable. -/
def IsNormal (p : Presentation) (t : AST) : Prop := oneStep p t = none

/-- Soundness: the normalizer's result is reachable from the input by many context rewrites. Every run
    of the runtime is a genuine reduction sequence of the presentation's semantics. -/
theorem eval_sound (p : Presentation) : ∀ (fuel : Nat) (t : AST), RewStepMany p t (eval p fuel t)
  | 0, t => by simp only [eval]; exact .refl
  | fuel + 1, t => by
      simp only [eval]
      split
      · rename_i t' hstep
        exact (RewStepMany.single (oneStep_sound p t hstep)).trans (eval_sound p fuel t')
      · exact .refl

/-- A normal term is a fixpoint of the normalizer. -/
theorem eval_fixed_of_normal (p : Presentation) (t : AST) (h : IsNormal p t) (fuel : Nat) :
    eval p (fuel + 1) t = t := by
  simp only [IsNormal] at h
  simp only [eval, h]

end MeTTaIL
