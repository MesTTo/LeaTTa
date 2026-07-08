-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Semantics.Normal
Layer: Semantics
Purpose: Completeness of the one-step reducer for base rewriting. `hasRedex` decides whether a base
  rewrite applies anywhere in a term (root or any subterm). The theorem `oneStep_isSome_eq_hasRedex`
  shows the executable reducer succeeds exactly when a redex exists, so together with `oneStep_sound`
  the engine is both sound and complete for base rewriting. The corollary `isNormal_iff_hasRedex_false`
  makes `IsNormal` meaningful: the runtime stops at a term precisely when no base rewrite applies
  anywhere in it.
Imports: MeTTaIL.Semantics.Eval
Trusted boundary: none (fully proved)
Main exports: hasRedex, hasRedexList, oneStep_isSome_eq_hasRedex, oneStepList_isSome_eq_hasRedexList,
  isNormal_iff_hasRedex_false
Open obligations: none for base rewriting; completeness in the presence of premised (conditional)
  rules is part of the conditional-rewrite work.
-/
import MeTTaIL.Semantics.Eval

namespace MeTTaIL

mutual
  /-- Whether a base rewrite applies anywhere in the term: at the root, or recursively in a `sexp`
      argument or a `Subst` component. -/
  def hasRedex (p : Presentation) : AST → Bool
    | .var x => !(baseReducts p (.var x)).isEmpty
    | .sexp l args => !(baseReducts p (.sexp l args)).isEmpty || hasRedexList p args
    | .subst b r v => !(baseReducts p (.subst b r v)).isEmpty || hasRedex p b || hasRedex p r
  /-- Whether any element of the list has a redex. -/
  def hasRedexList (p : Presentation) : List AST → Bool
    | [] => false
    | a :: as => hasRedex p a || hasRedexList p as
end

mutual
  /-- Completeness: the executable reducer succeeds exactly when a base redex exists. -/
  theorem oneStep_isSome_eq_hasRedex (p : Presentation) :
      ∀ (t : AST), (oneStep p t).isSome = hasRedex p t
    | .var x => by
        simp only [oneStep, hasRedex]
        cases baseReducts p (.var x) <;> simp
    | .sexp l args => by
        simp only [oneStep, hasRedex]
        cases baseReducts p (.sexp l args) <;>
          simp [Option.isSome_map, oneStepList_isSome_eq_hasRedexList p args]
    | .subst b r v => by
        simp only [oneStep, hasRedex]
        cases baseReducts p (.subst b r v) with
        | cons s rest => simp
        | nil =>
            simp only [List.isEmpty_nil, Bool.not_true, Bool.false_or]
            cases hb : oneStep p b with
            | some b' =>
                have := oneStep_isSome_eq_hasRedex p b
                rw [hb] at this; simp at this
                simp [this]
            | none =>
                have hbn := oneStep_isSome_eq_hasRedex p b
                rw [hb] at hbn; simp at hbn
                simp only [Option.isSome_map, oneStep_isSome_eq_hasRedex p r, hbn, Bool.false_or]
  /-- List version of completeness. -/
  theorem oneStepList_isSome_eq_hasRedexList (p : Presentation) :
      ∀ (args : List AST), (oneStepList p args).isSome = hasRedexList p args
    | [] => by simp [oneStepList, hasRedexList]
    | a :: as => by
        simp only [oneStepList, hasRedexList]
        cases ha : oneStep p a with
        | some a' =>
            have := oneStep_isSome_eq_hasRedex p a
            rw [ha] at this; simp at this
            simp [this]
        | none =>
            have han := oneStep_isSome_eq_hasRedex p a
            rw [ha] at han; simp at han
            simp only [Option.isSome_map, oneStepList_isSome_eq_hasRedexList p as, han, Bool.false_or]
end

/-- `IsNormal` means exactly that no base rewrite applies anywhere in the term. -/
theorem isNormal_iff_hasRedex_false (p : Presentation) (t : AST) :
    IsNormal p t ↔ hasRedex p t = false := by
  unfold IsNormal
  rw [← oneStep_isSome_eq_hasRedex p t]
  simp [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]

end MeTTaIL
