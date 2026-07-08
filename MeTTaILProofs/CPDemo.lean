-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaILProofs.CPDemo
Layer: Proofs
Purpose: Non-vacuity witnesses for the effective critical-pair machinery. These demonstrate that the
  verified unifier actually computes (it is not a degenerate always-`none` function) and that the effective
  criterion `CPJ_of_check` is genuinely usable: it derives `CPJ projSys` for the projection system
  `f(x) -> x` through the unify-based check, an independent route to the result `cpj_projSys` proves directly.
Imports: MeTTaILProofs.CPDecide (unify, CPJ_of_check, the renaming machinery), MeTTaILProofs.CriticalPairs
  (projSys)
Trusted boundary: none (fully proved)
Main exports: cpj_projSys_via_check
-/
import MeTTaILProofs.CPDecide
import MeTTaILProofs.CPRuntime

namespace MeTTaIL.CP

/-! ### The unifier computes (it is a real algorithm, not degenerate) -/

/-- `f(x)` unifies with `f(a)` (the algorithm succeeds on a genuinely unifiable input). -/
example : (unify 10 [(.app "f" [.var 0], .app "f" [.app "a" []])]).isSome = true := by rfl

/-- A first-order pair with two distinct heads does not unify. -/
example : unify 10 [(.app "f" [.var 0], .app "g" [.var 0])] = none := by rfl

/-- The occurs check rejects `x = f(x)` (no finite unifier). -/
example : unify 10 [(.var 0, .app "f" [.var 0])] = none := by rfl

/-! ### `CPJ_of_check` is usable: the projection system via the effective criterion -/

/-- The projection rule introduces no fresh right-hand-side variables. -/
theorem hvars_projSys' : ∀ l r, (l, r) ∈ projSys → ∀ n ∈ varsFin r, n ∈ varsFin l := by
  intro l r hm n hn
  simp only [projSys, List.mem_singleton, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  simpa [varsFin, varsFinList] using hn

/-- `CPJ projSys` derived through the effective unify-based critical-pair check `CPJ_of_check` (not the
    direct `cpj_projSys`). Every overlap of `f(x) -> x` unifies the two sides of the critical pair, so each
    critical pair is joinable by reflexivity, and the criterion discharges. This witnesses that the
    Knuth-Bendix-Huet criterion is genuinely applicable, not vacuous. -/
theorem cpj_projSys_via_check : CPJ projSys := by
  apply CPJ_of_check hvars_projSys'
  intro l1 r1 l2 r2 hm1 hm2 o lo ho
  simp only [projSys, List.mem_singleton, Prod.mk.injEq] at hm1 hm2
  obtain ⟨rfl, rfl⟩ := hm1
  obtain ⟨rfl, rfl⟩ := hm2
  intro f' σ hf
  have hsd := unify_sound f' _ σ hf _ (List.mem_singleton.mpr rfl)
  -- positions of `f(x)`: root `[]` (lo = f(x)) and the argument `[0]` (lo = x); nothing else
  cases o with
  | nil =>
      simp only [subAt, Option.some.injEq] at ho; subst ho
      -- the two critical-pair sides coincide because the unifier identifies them
      have heq : subst σ (.var 0)
          = repAt (subst σ (.app "f" [.var 0])) []
              (subst σ (shift (bound (.app "f" [.var 0])) (.var 0))) := by
        simpa only [repAt, subst, shift, shiftList, substList, FOTerm.app.injEq, List.cons.injEq,
          Nat.zero_add, and_true, true_and] using hsd
      rw [heq]; exact ⟨_, .refl, .refl⟩
  | cons i o' =>
      cases i with
      | zero =>
          cases o' with
          | nil =>
              simp only [subAt, List.getElem?_cons_zero, Option.some.injEq] at ho; subst ho
              have heq : subst σ (.var 0)
                  = repAt (subst σ (.app "f" [.var 0])) [0]
                      (subst σ (shift (bound (.app "f" [.var 0])) (.var 0))) := by
                simpa only [subst, shift, shiftList, repAt, subAt, List.getElem?_cons_zero,
                  List.set_cons_zero, substList, Nat.zero_add] using hsd
              rw [heq]; exact ⟨_, .refl, .refl⟩
          | cons _ _ => simp [subAt] at ho
      | succ j => simp [subAt] at ho

/-! ### End-to-end: a concrete terminating confluent system, transported to the runtime

This discharges the confluence transport `RewStep_confluent_on_emb` on a genuine non-trivial confluent
system, `projSys` (f(x) -> x). It terminates (the rule strictly shrinks the term), so it is fully
`Confluent` (not merely locally), and the bridge then certifies that the runtime `RewStep` is confluent on
the embedded fragment. -/

/-- Setting a list element to something smaller strictly shrinks the list size. -/
theorem sizeList_set_lt : ∀ {args : List FOTerm} {i : Nat} {a x : FOTerm},
    args[i]? = some a → size x < size a → sizeList (args.set i x) < sizeList args
  | _ :: _, 0, _, _, hi, hlt => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
      simp only [List.set_cons_zero, sizeList]; omega
  | _ :: as, i + 1, a, x, hi, hlt => by
      simp only [List.getElem?_cons_succ] at hi
      simp only [List.set_cons_succ, sizeList]
      have := sizeList_set_lt (args := as) hi hlt; omega

/-- Replacing a subterm by something strictly smaller strictly shrinks the whole term. -/
theorem repAt_size_lt : ∀ {t : FOTerm} {p : Pos} {s w : FOTerm},
    subAt t p = some s → size w < size s → size (repAt t p w) < size t
  | _, [], _, _, hsub, hlt => by
      simp only [subAt, Option.some.injEq] at hsub; subst hsub; simpa [repAt] using hlt
  | .var _, _ :: _, _, _, hsub, _ => by simp [subAt] at hsub
  | .app _ args, _ :: _, _, _, hsub, hlt => by
      simp only [subAt] at hsub
      split at hsub
      · rename_i a hai
        simp only [repAt, hai, size]
        have ha := repAt_size_lt hsub hlt
        have := sizeList_set_lt (args := args) hai ha; omega
      · simp at hsub

/-- Every projection step strictly shrinks the term. -/
theorem rstep_projSys_size_lt {a b : FOTerm} (h : Rstep projSys a b) : size b < size a := by
  obtain ⟨p, l, r, σ, hmem, hsub, hrep⟩ := h
  simp only [projSys, List.mem_singleton, Prod.mk.injEq] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  subst hrep
  refine repAt_size_lt hsub ?_
  simp only [subst, substList, size, sizeList]; omega

/-- The projection system terminates. -/
theorem wf_projSys : WellFounded (fun b a => Rstep projSys a b) :=
  Subrelation.wf (fun h => rstep_projSys_size_lt h) (InvImage.wf size Nat.lt_wfRel.wf)

/-- The projection system is (fully) confluent: left-linear + joinable critical pairs + terminating. -/
theorem confluent_projSys : Confluent (Rstep projSys) :=
  confluent_of_CPJ leftLinear_projSys cpj_projSys wf_projSys

/-- The headline confluence transport, instantiated end-to-end on the concrete terminating confluent system
    `projSys`: the runtime `RewStep` is confluent on the embedded projection-system fragment. -/
example {u1 u2 : AST}
    (h1 : Relation.ReflTransGen (RewStep (embPres vname projSys))
            (emb vname (.app "f" [.app "a" []])) u1)
    (h2 : Relation.ReflTransGen (RewStep (embPres vname projSys))
            (emb vname (.app "f" [.app "a" []])) u2) :
    Joinable (RewStep (embPres vname projSys)) u1 u2 :=
  RewStep_confluent_on_emb vname vname_injective hvars_projSys confluent_projSys h1 h2

/-! ### Binder fragment: a `Subst`-RHS reduction is subject-reduction-correct (non-vacuity for #2) -/

/-- A concrete witness that the binder-fragment subject reduction is usable: a rule whose right-hand side is
    the explicit substitution `subst (var z) (var u) z` ("substitute `u` for `z` in `z`") reduces, via
    `inst`, to `var u`, and the reduct is well-sorted at `u`'s sort. This is the shape of the rho-calculus
    COMM reduct, the case the first-order subject reduction excludes. -/
example {p : Presentation} {Γ : Ctx} {c : Cat} (hu : Γ.lookup "u" = some c) :
    WellSorted p Γ (AST.inst [] (.subst (.var (.base "z")) (.var (.base "u")) (.base "z"))) c :=
  reduces_subst_wellSorted (cw := c) (WellSorted.var (by simp [AST.instSubstTarget, Ctx.extendPath])) (WellSorted.var hu)

/-- The captured-bound-variable (alpha) case, the one the freshness-restricted version excluded: the bound
    variable `z` is matched (here to the runtime variable `y`), so `inst` remaps the substitution target to
    `y`. The reduct `subst (var y) (inst r) (inst b)` is still well-sorted, witnessed through the
    `instSubstTarget`/`extendPath` machinery. -/
example {p : Presentation} {Γ : Ctx} {c : Cat} (hu : Γ.lookup "u" = some c) :
    WellSorted p Γ
      (AST.inst [("z", .var (.base "y"))]
        (.subst (.var (.base "z")) (.var (.base "u")) (.base "z"))) c :=
  reduces_subst_wellSorted (cw := c) (WellSorted.var (by simp [AST.instSubstTarget, Ctx.extendPath])) (WellSorted.var hu)

/-! ### Full-language matcher correctness covers Subst patterns (non-vacuity for #2)

The matcher handles `Subst` patterns, and `matchPat_iff_instStruct` certifies them against STRUCTURAL
instantiation `instStruct` (which keeps the `Subst` node), not `inst` (which resolves it). These witnesses
show the distinction is real, so the `SubstFree` restriction is genuinely lifted. -/

/-- A `Subst` pattern matches a `Subst` term, binding the pattern variables in body and replacement. -/
example :
    AST.matchPat (.subst (.var (.base "x")) (.var (.base "y")) (.base "z"))
      (.subst (.sexp (.id "a") []) (.sexp (.id "b") []) (.base "z")) []
      = some [("y", .sexp (.id "b") []), ("x", .sexp (.id "a") [])] := rfl

/-- The matcher inverts `instStruct`: structural instantiation rebuilds the matched `Subst` term. -/
example :
    AST.instStruct [("y", .sexp (.id "b") []), ("x", .sexp (.id "a") [])]
      (.subst (.var (.base "x")) (.var (.base "y")) (.base "z"))
      = .subst (.sexp (.id "a") []) (.sexp (.id "b") []) (.base "z") := rfl

/-- Why `instStruct` and not `inst`: `inst` RESOLVES the explicit substitution (here `subst1 z`), collapsing
    the `Subst` node to `a`, so the structural matcher could not be correct against `inst` on a `Subst`
    pattern. This is exactly the gap the `instStruct`-based correctness closes. -/
example :
    AST.inst [("y", .sexp (.id "b") []), ("x", .sexp (.id "a") [])]
      (.subst (.var (.base "x")) (.var (.base "y")) (.base "z"))
      = .sexp (.id "a") [] := rfl

/-- The headline `matchPat_iff_instStruct` instantiated at a `Subst` pattern (no `SubstFree` restriction). -/
example :
    (∃ bnds, AST.matchPat (.subst (.var (.base "x")) (.var (.base "y")) (.base "z"))
        (.subst (.sexp (.id "a") []) (.sexp (.id "b") []) (.base "z")) [] = some bnds) ↔
    (∃ σ, AST.instStruct σ (.subst (.var (.base "x")) (.var (.base "y")) (.base "z"))
        = .subst (.sexp (.id "a") []) (.sexp (.id "b") []) (.base "z")) :=
  matchPat_iff_instStruct

end MeTTaIL.CP
