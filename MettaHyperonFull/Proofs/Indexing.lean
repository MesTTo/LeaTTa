-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.Indexing
Layer: Proofs
Purpose: Soundness of first-argument rule indexing, the semantic half. Proves matchAtoms_headKey: if
  a query is headed by symbol k and a rule left-hand side matches it, then that left-hand side is
  headed by the same k or is head-less. A rule in a different head bucket can never match, so
  restricting candidates to k's bucket plus the head-less rules loses nothing.
Imports: MettaHyperonFull.Proofs.Basic
Trusted boundary: none (fully proved)
Main exports: matchAtoms_headKey, headKey_some, matchAll_nil, matchAll_fst, matchAtoms_sym_expr,
  matchAtoms_expr_sym
Open obligations: none. The syntactic companion characterising MinEnv.candidates is in
  IndexingComplete.lean.
-/
import MettaHyperonFull.Proofs.Basic

/-!
# Metatheory: first-argument rule indexing is sound

Hyperon's interpreter does not scan the whole atomspace for every reduction: it indexes equality
rules by the head symbol of their left-hand side and, to reduce `toEval`, only consults the rules
whose head matches `toEval`'s (its `AtomIndex`). The kernel does the same: `MinEnv.ruleIndex`
buckets `(= lhs rhs)` rules by `headKey lhs`, and `MinEnv.candidates` returns the bucket for the
query's head together with the head-less (`varRules`) rules (`Minimal/Interpreter.lean`). See
the Improvements over Hyperon appendix in the book (the `Space::visit` undercounting case).

For that optimisation to be *sound* it must never drop a rule that could actually fire. This
file proves the semantic guarantee:

> **`matchAtoms_headKey`**: if `toEval` is headed by symbol `k` and a rule LHS matches it, then
> the LHS is headed by the *same* `k`, or it is head-less (`headKey = none`, i.e. variable- or
> grounded-headed).

A rule sitting in a *different* head bucket can therefore never match, so restricting the
candidate set to `k`'s bucket union the head-less rules loses nothing.

The syntactic companion (that `MinEnv.candidates` returns `k`'s bucket union the
head-less rules, characterised against the flat rule list) is proved on top of this in
`IndexingComplete.lean`.

Note on `matchAtomsWith`: the `gnd`-free reasoning needs `Atom`'s `==` to *reduce*, which is
why the kernel uses a hand-written structural `BEq Atom` (`Core/Atom.lean`) rather than the
derived one (the derived instance is well-founded and opaque even to `decide`).
-/

namespace Metta
open Metta.Minimal

/-- `headKey a = some k` holds exactly when `a` is the symbol `k` or an expression headed by the
symbol `k`: the two shapes that occupy a head bucket. -/
theorem headKey_some {a : Atom} {k : String} (h : headKey a = some k) :
    a = Atom.sym k ∨ ∃ rest, a = Atom.expr (Atom.sym k :: rest) := by
  cases a with
  | sym s => left; simp only [headKey, Option.some.injEq] at h; rw [h]
  | var v => simp [headKey] at h
  | gnd g => simp [headKey] at h
  | expr xs =>
      cases xs with
      | nil => simp [headKey] at h
      | cons x xs =>
          cases x with
          | sym s => right; exact ⟨xs, by simp only [headKey, Option.some.injEq] at h; rw [h]⟩
          | var v => simp [headKey] at h
          | gnd g => simp [headKey] at h
          | expr ys => simp [headKey] at h

/-- With an empty accumulator the pointwise matcher yields nothing: there is no binding set to
extend, so every branch dies. -/
theorem matchAll_nil (custom : Option GroundMatcher) (xs ys : List Atom) :
    matchAll custom [] xs ys = [] := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [matchAll]
  | cons x xs ih => cases ys with
    | nil => simp [matchAll]
    | cons y ys => simp only [matchAll, List.flatMap_nil]; exact ih ys

/-- The heads must match first: if `matchAll … (x :: xs) (y :: ys)` is non-empty then matching the
heads `x` and `y` already succeeds. (If the heads failed, the accumulator would collapse to `[]`
and `matchAll_nil` would finish the list off as empty.) -/
theorem matchAll_fst (custom : Option GroundMatcher) (x y : Atom) (xs ys : List Atom)
    (h : matchAll custom [[]] (x :: xs) (y :: ys) ≠ []) : matchAtomsWith custom x y ≠ [] := by
  intro hsub
  apply h
  simp only [matchAll, hsub, List.flatMap_nil, List.flatMap_cons]
  exact matchAll_nil custom xs ys

/-- A symbol and an expression have different metatypes, so the `==` of the catch-all matcher
branch is `false` (reduces structurally with the hand-written `BEq Atom`). -/
theorem beq_sym_expr (a : String) (xs : List Atom) :
    (Atom.sym a == Atom.expr xs) = false := rfl

theorem beq_expr_sym (xs : List Atom) (a : String) :
    (Atom.expr xs == Atom.sym a) = false := rfl

theorem equiv_sym_expr (a : String) (xs : List Atom) :
    Atom.equiv (Atom.sym a) (Atom.expr xs) = false := rfl

theorem equiv_expr_sym (xs : List Atom) (a : String) :
    Atom.equiv (Atom.expr xs) (Atom.sym a) = false := rfl

/-- A symbol pattern never matches an expression (different metatypes). -/
theorem matchAtoms_sym_expr (a : String) (xs : List Atom) :
    matchAtoms (Atom.sym a) (Atom.expr xs) = [] := by
  simp [matchAtoms, matchAtomsWith, equiv_sym_expr]

/-- An expression pattern never matches a symbol (different metatypes). -/
theorem matchAtoms_expr_sym (xs : List Atom) (a : String) :
    matchAtoms (Atom.expr xs) (Atom.sym a) = [] := by
  simp [matchAtoms, matchAtomsWith, equiv_expr_sym]

/-- **Matching forces head agreement.** If the query `toEval` is headed by symbol `k` and a rule
left-hand side `lhs` matches it, then `lhs` is headed by the *same* `k`, or `lhs` is head-less
(`headKey lhs = none`). So first-argument indexing, which offers `toEval` only the rules
in head bucket `k` together with the head-less rules, never hides a rule that could fire: it is
sound. -/
theorem matchAtoms_headKey {lhs toEval : Atom} {k : String}
    (hk : headKey toEval = some k) (hm : matchAtoms lhs toEval ≠ []) :
    headKey lhs = some k ∨ headKey lhs = none := by
  rcases hl : headKey lhs with _ | k'
  · -- `lhs` is head-less: it lives in `varRules`, always a candidate.
    right; rfl
  · -- `lhs` is headed by `k'`; matching forces `k' = k`.
    left
    rw [Option.some.injEq]
    rcases headKey_some hl with rfl | ⟨ls, rfl⟩ <;> rcases headKey_some hk with rfl | ⟨rs, rfl⟩
    · -- both bare symbols: the matcher compares them by `String` equality.
      simp only [matchAtoms, matchAtomsWith] at hm
      split at hm
      · rename_i h; exact eq_of_beq h
      · exact absurd rfl hm
    · -- symbol vs expression: cannot match (vacuous).
      exact absurd (matchAtoms_sym_expr k' (Atom.sym k :: rs)) hm
    · -- expression vs symbol: cannot match (vacuous).
      exact absurd (matchAtoms_expr_sym (Atom.sym k' :: ls) k) hm
    · -- both expressions: the head elements must match, again by `String` equality.
      have hraw : matchAll none [[]]
          (Atom.sym k' :: ls) (Atom.sym k :: rs) ≠ [] := by
        intro hnone
        apply hm
        simp [matchAtoms, matchAtomsWith, hnone]
      have hfst := matchAll_fst none (Atom.sym k') (Atom.sym k) ls rs
        hraw
      simp only [matchAtomsWith] at hfst
      split at hfst
      · rename_i h; exact eq_of_beq h
      · exact absurd rfl hfst

end Metta
